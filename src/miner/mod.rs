// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022-2023 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

#![allow(deprecated)]

use crate::consensus::Difficulty;
use crate::primitives::{Hash256, PowBlockHeader};
use blake2::{Blake2b512, Blake2s256, Digest};
use crossbeam_channel::{unbounded, Receiver, Sender, TryRecvError};
use jh_x86_64::{Digest as JhDigest, Jh256};
use parking_lot::Mutex;
use sha2::{Sha256, Sha512, Sha512_256};
use sha3::{Keccak256, Keccak512, Sha3_256, Sha3_512};
use std::fmt;
use std::thread;
use std::thread::JoinHandle;
use triomphe::Arc;

#[derive(Debug)]
pub enum HashAlgorithm {
    Blake2s256,
    Blake2b512,
    Sha256,
    Keccak256,
    JH,
    Fugue,
}

impl HashAlgorithm {
    /// Hash bytes using algorithm
    pub fn hash(&self, bytes: &[u8]) -> Hash256 {
        let mut out = Hash256([0; 32]);

        match self {
            Self::Blake2s256 => {
                let mut hasher = Blake2s256::new();
                hasher.update(bytes);
                let hash = hasher.finalize();
                out.0.copy_from_slice(&hash[..]);
                out
            }

            Self::Blake2b512 => {
                let mut hasher = Blake2b512::new();
                hasher.update(bytes);
                let hash = hasher.finalize();
                out.0.copy_from_slice(&hash[..32]);
                out
            }

            Self::Sha256 => {
                let mut hasher = Sha256::new();
                hasher.update(bytes);
                let hash = hasher.finalize();
                out.0.copy_from_slice(&hash[..]);
                out
            }

            Self::Keccak256 => {
                let mut hasher = Keccak256::new();
                hasher.update(bytes);
                let hash = hasher.finalize();
                out.0.copy_from_slice(&hash[..]);
                out
            }

            Self::JH => {
                let mut hasher = Jh256::new();
                hasher.input(bytes);
                let hash = hasher.result();
                out.0.copy_from_slice(&hash[..]);
                out
            }

            Self::Fugue => {
                out.0 = crate::primitives::hash_bytes_fugue256(bytes);
                out
            }
        }
    }

    pub fn deterministic_random(bytes: &[u8]) -> Self {
        let hash = blake3::hash(bytes);
        let key = &hash.as_bytes()[..8];
        let mut k = [0; 8];
        k.copy_from_slice(key);
        let key = u64::from_le_bytes(k);
        let out = jump_consistent_hash::hash(key, 6);

        match out {
            0 => Self::Blake2s256,
            1 => Self::Blake2b512,
            2 => Self::Sha256,
            3 => Self::Keccak256,
            4 => Self::JH,
            5 => Self::Fugue,
            _ => unreachable!(),
        }
    }

    pub fn diff_idx_r1(&self) -> usize {
        match self {
            Self::Blake2s256 => 2,
            Self::Blake2b512 => 4,
            Self::Sha256 => 6,
            Self::Keccak256 => 8,
            Self::JH => 10,
            Self::Fugue => 12,
        }
    }

    pub fn diff_idx_r2(&self) -> usize {
        match self {
            Self::Blake2s256 => 3,
            Self::Blake2b512 => 5,
            Self::Sha256 => 7,
            Self::Keccak256 => 9,
            Self::JH => 11,
            Self::Fugue => 13,
        }
    }
}

pub enum PowAlgorithm {
    /// ASIC friendly algorithm. One is chosen at random per epoch
    RandomHash(HashAlgorithm),

    /// GR proof of work - CPU friendly
    GR,
}

impl PowAlgorithm {
    pub fn hash(&self, bytes: &[u8]) -> Hash256 {
        match self {
            Self::RandomHash(algo) => algo.hash(bytes),
            Self::GR => unreachable!(),
        }
    }

    pub fn diff_idx_r1(&self) -> usize {
        match self {
            Self::GR => 0,
            Self::RandomHash(algo) => algo.diff_idx_r1(),
        }
    }

    pub fn diff_idx_r2(&self) -> usize {
        match self {
            Self::GR => 1,
            Self::RandomHash(algo) => algo.diff_idx_r2(),
        }
    }
}

impl fmt::Debug for PowAlgorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RandomHash(algo) => f.debug_tuple("RandomHash").field(algo).finish(),

            Self::GR => f.debug_tuple("GR").finish(),
        }
    }
}

pub struct Miner {
    threads: Vec<JoinHandle<()>>,
    ctrl_recv: Vec<Receiver<MinerCtrl>>,
    ctrl_send: Vec<Sender<MinerCtrl>>,
    miner_states: Vec<Arc<Mutex<MinerState>>>,
}

impl Miner {
    pub fn new() -> Self {
        let num_threads = 1;
        let mut threads = Vec::with_capacity(num_threads);
        let mut ctrl_recv = Vec::with_capacity(num_threads);
        let mut ctrl_send = Vec::with_capacity(num_threads);
        let mut miner_states = Vec::with_capacity(num_threads);

        for _ in 0..num_threads {
            let (s1, r1): (Sender<MinerCtrl>, Receiver<MinerCtrl>) = unbounded();
            let (s2, r2): (Sender<MinerCtrl>, Receiver<MinerCtrl>) = unbounded();
            let state = Arc::new(Mutex::new(MinerState::Paused));
            let state_clone = state.clone();
            threads.push(thread::spawn(move || {
                let mut state = state_clone;
                let ctrl_recv = r2;
                let ctrl_send = s1;

                loop {
                    let mut state = state.lock();
                    match ctrl_recv.try_recv() {
                        Ok(MinerCtrl::Pause) => {
                            *state = MinerState::Paused;
                        }

                        Ok(MinerCtrl::Exit) => {
                            break;
                        }

                        Ok(MinerCtrl::Start(mut header)) => {
                            header.zero_nonce();
                            *state = MinerState::Running(header);
                        }

                        Ok(_) => {
                            panic!("Unexpected variant");
                        }

                        Err(TryRecvError::Empty) => match *state {
                            MinerState::Paused => {
                                thread::sleep_ms(1);
                            }

                            MinerState::Running(ref mut header) => {
                                match header.map_height_to_algo() {
                                    PowAlgorithm::GR => {
                                        let key = header.prev_hash.0;
                                        let header_bytes = header.to_bytes(); // TODO: Cache this
                                        let out = crate::consensus::PowOutput::new(
                                            crate::primitives::hash_arb_bytes_gr(
                                                &header_bytes,
                                                key,
                                            ),
                                        );
                                        let idx = match header.round() {
                                            1 => 0,
                                            2 => 12,
                                            _ => unreachable!(),
                                        };

                                        if out.meets_difficulty(Difficulty::new(header.bits(idx))) {
                                            header.hash = Some(out.into());
                                            ctrl_send
                                                .send(MinerCtrl::FoundNonce(header.clone()))
                                                .unwrap();
                                            *state = MinerState::Paused;
                                            continue;
                                        }

                                        if header.increment_nonce().is_none() {
                                            ctrl_send.send(MinerCtrl::ExhaustedNonces).unwrap();
                                            *state = MinerState::Paused;
                                            continue;
                                        }
                                    }

                                    PowAlgorithm::RandomHash(algo) => {
                                        let out = algo.hash(&header.to_bytes());
                                        let idx = match header.round() {
                                            1 => algo.diff_idx_r1(),
                                            2 => algo.diff_idx_r2(),
                                            _ => unreachable!(),
                                        };

                                        if out.meets_difficulty(header.bits(idx)) {
                                            header.hash = Some(out);
                                            ctrl_send
                                                .send(MinerCtrl::FoundNonce(header.clone()))
                                                .unwrap();
                                            *state = MinerState::Paused;
                                            continue;
                                        }

                                        if header.increment_nonce().is_none() {
                                            ctrl_send.send(MinerCtrl::ExhaustedNonces).unwrap();
                                            *state = MinerState::Paused;
                                            continue;
                                        }
                                    }
                                }
                            }
                        },

                        Err(err) => {
                            //println!("Miner error: {:?}", err);
                            break;
                        }
                    }
                }
                //ctrl_send.send(MinerCtrl::Exit).unwrap();
            }));
            ctrl_recv.push(r1);
            ctrl_send.push(s2);
            miner_states.push(state);
        }

        Miner {
            threads,
            ctrl_recv,
            ctrl_send,
            miner_states,
        }
    }

    pub fn status(&self) -> MinerStatus {
        match &*self.miner_states[0].lock() {
            MinerState::Running(_) => MinerStatus::Running,
            MinerState::Paused => MinerStatus::Paused,
        }
    }

    pub fn start(&self, header: PowBlockHeader) {
        for i in 0..1 {
            self.ctrl_send[i]
                .send(MinerCtrl::Start(header.clone()))
                .unwrap();
        }
    }

    pub fn block_wait_result(&self) -> Option<PowBlockHeader> {
        loop {
            match self.try_recv_result() {
                Some(result) => return Some(result),
                None => {}
            }

            thread::sleep_ms(1);
        }
    }

    pub fn try_recv_result(&self) -> Option<PowBlockHeader> {
        for i in 0..1 {
            match self.ctrl_recv[i].try_recv() {
                Ok(MinerCtrl::FoundNonce(header)) => {
                    for j in 0..1 {
                        self.ctrl_send[j].send(MinerCtrl::Pause).unwrap();
                    }

                    return Some(header);
                }

                Ok(_) => {
                    panic!("Unexpected variant");
                }

                Err(TryRecvError::Empty) => {}

                Err(err) => {
                    panic!("An error occured: {err:?}");
                }
            }
        }

        None
    }
}

#[derive(Clone, Copy, Debug)]
pub enum MinerStatus {
    Paused,
    Running,
}

#[derive(Clone, Debug)]
enum MinerState {
    Paused,
    Running(PowBlockHeader),
}

enum MinerCtrl {
    FoundNonce(PowBlockHeader),
    ExhaustedNonces,
    Pause,
    Start(PowBlockHeader),
    Exit,
}
