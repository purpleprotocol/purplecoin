// Copyright (c) 2022 Octavian Oncescu
// Copyright (c) 2022 The Purplecoin Core developers
// Licensed under the Apache License, Version 2.0 see LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0 or the MIT license, see
// LICENSE-MIT or http://opensource.org/licenses/MIT

use crate::primitives::{
    Address, ColouredAddress, Hash160, Hash256, Output, PublicKey, Transaction,
};
use crate::vm::Script;
use accumulator::group::{Codec, Rsa2048};
use accumulator::Witness;
use bincode::{Decode, Encode};
use chacha20poly1305::aead::{Aead, NewAead};
use chacha20poly1305::{Key, XChaCha20Poly1305, XNonce};
use chrono::prelude::*;
use rand::prelude::*;
use schnorrkel::derive::{ChainCode, ExtendedKey};
use schnorrkel::keys::{ExpansionMode, MiniSecretKey};
use schnorrkel::SecretKey as SchnorrSecretKey;
use std::collections::HashMap;
use std::fmt;
use std::fs;
use std::marker::PhantomData;
use std::path::PathBuf;
use zeroize::Zeroize;

const SEED_BYTES: usize = 64;
const ADDRESS_BATCH_SIZE: usize = 1000;

#[derive(Encode, Decode, Debug, PartialEq)]
pub enum EncryptionAlgo {
    XChaCha20Poly1305,
    AES256GCM,
}

#[derive(Encode, Decode, PartialEq)]
/// Encrypted entry that can be serialized to bytes
pub struct EncryptedEntry<T: Encode + Decode> {
    /// Encryption algorithm
    algo: EncryptionAlgo,

    /// Nonce
    nonce: Vec<u8>,

    /// Ciphertext
    ciphertext: Vec<u8>,

    /// Phantom
    phantom: PhantomData<T>,
}

impl<T: Encode + Decode> fmt::Debug for EncryptedEntry<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("XPub")
            .field("algo", &self.algo)
            .field("nonce", &hex::encode(&self.nonce))
            .field("data", &"[ENCRYPTED]")
            .finish()
    }
}

impl<T: Encode + Decode> EncryptedEntry<T> {
    /// Creates an encrypted entry from data with key using XChacha20Poly1305
    pub fn xchacha20poly1305(key: &[u8], data: T) -> Result<Self, &'static str> {
        let config = bincode::config::standard()
            .with_little_endian()
            .with_variable_int_encoding()
            .skip_fixed_array_length();
        let mut data = bincode::encode_to_vec(data, config).unwrap();
        let mut rng = rand::thread_rng();
        let key = Key::from_slice(key);
        let cipher = XChaCha20Poly1305::new(key);
        let nonce_bytes: [u8; 24] = rng.gen();
        let nonce = XNonce::from_slice(&nonce_bytes);

        let ciphertext = cipher
            .encrypt(nonce, data.as_ref())
            .map_err(|_| "encryption failure!")?;

        data.zeroize();

        Ok(EncryptedEntry {
            algo: EncryptionAlgo::XChaCha20Poly1305,
            nonce: nonce_bytes.to_vec(),
            ciphertext,
            phantom: PhantomData,
        })
    }

    /// Creates an encrypted entry from data with key using AES256GCM
    pub fn aes256gcm(key: &[u8], data: T) -> Result<Self, &'static str> {
        unimplemented!();
    }

    /// Decrypts the ciphertext using the provided key
    pub fn decrypt(&self, key: &[u8]) -> Result<T, &'static str> {
        let config = bincode::config::standard()
            .with_little_endian()
            .with_variable_int_encoding()
            .skip_fixed_array_length();

        match self.algo {
            EncryptionAlgo::XChaCha20Poly1305 => {
                unimplemented!();
            }

            EncryptionAlgo::AES256GCM => {
                unimplemented!();
            }
        }
    }
}

#[derive(Encode, Decode, Zeroize, Clone, PartialEq)]
pub struct XPub {
    version: u32,
    depth: u8,
    fingerprint: [u8; 4],
    child_number: u32,
    chain_code: [u8; 32],
    pub_key: PublicKey,
}

impl XPub {
    pub fn derive_next(&self) -> Self {
        let address = self.to_address();
        let mut fingerprint = [0; 4];
        fingerprint.copy_from_slice(&address.as_bytes()[..4]);

        let extended_key = ExtendedKey {
            chaincode: ChainCode(self.chain_code),
            key: self.pub_key.0,
        };
        let child_number = self.child_number + 1;

        XPub {
            version: 0x0488B21E,
            chain_code: self.chain_code,
            fingerprint,
            child_number,
            depth: 0x01,
            pub_key: PublicKey(
                extended_key
                    .derived_key_simple(format!("{child_number}"))
                    .key,
            ),
        }
    }

    pub fn to_address(&self) -> Address {
        self.pub_key.to_address()
    }
}

impl fmt::Debug for XPub {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("XPub")
            .field("version", &format!("0x{:x}", self.version))
            .field("chain_code", &hex::encode(self.chain_code))
            .field("fingerprint", &hex::encode(self.fingerprint))
            .field("child_number", &self.child_number)
            .field("depth", &self.depth)
            .field("pub_key", &hex::encode(self.pub_key.0))
            .finish()
    }
}

impl XPriv {
    pub fn derive_next(&self) -> Self {
        let mut hasher = blake3::Hasher::new();
        hasher.update(&self.secret_key);
        let mut out = hasher.finalize_xof();
        let mut fingerprint = [0; 4];
        out.fill(&mut fingerprint);

        let extended_key = ExtendedKey {
            chaincode: ChainCode(self.chain_code),
            key: SchnorrSecretKey::from_bytes(&self.secret_key).unwrap(),
        };
        let child_number = self.child_number + 1;

        XPriv {
            version: 0x0488ADE4,
            chain_code: self.chain_code,
            fingerprint,
            child_number,
            depth: 0x01,
            secret_key: extended_key
                .derived_key_simple(format!("{child_number}"))
                .key
                .to_bytes(),
        }
    }
}

#[derive(Encode, Decode, Zeroize, Clone, Debug, PartialEq)]
#[zeroize(drop)]
pub struct XPriv {
    version: u32,
    depth: u8,
    fingerprint: [u8; 4],
    child_number: u32,
    chain_code: [u8; 32],
    secret_key: [u8; 64],
}

#[derive(Encode, Decode, Zeroize, Debug)]
pub struct XKeypair {
    pub pub_key: XPub,
    pub secret_key: XPriv,
}

impl XKeypair {
    pub fn new_master(
        secret: &[u8],
        chain_code: &[u8],
        fingerprint: [u8; 4],
        depth: u8,
        child_number: u32,
    ) -> Self {
        let mut chain_code_fixed = [0; 32];
        chain_code_fixed.copy_from_slice(chain_code);
        let mut mini_secret = MiniSecretKey::from_bytes(secret).unwrap();
        let mut keypair = mini_secret.expand_to_keypair(ExpansionMode::Uniform);

        let xkeypair = XKeypair {
            pub_key: XPub {
                version: 0x0488B21E,
                chain_code: chain_code_fixed,
                fingerprint,
                child_number,
                depth,
                pub_key: PublicKey::from_bytes(&keypair.public.to_bytes()).unwrap(),
            },
            secret_key: XPriv {
                version: 0x0488ADE4,
                chain_code: chain_code_fixed,
                fingerprint,
                child_number,
                depth,
                secret_key: keypair.secret.to_bytes(),
            },
        };

        keypair.zeroize();
        mini_secret.zeroize();

        xkeypair
    }

    pub fn derive_next(&self) -> Self {
        XKeypair {
            pub_key: self.pub_key.derive_next(),
            secret_key: self.secret_key.derive_next(),
        }
    }

    pub fn pub_key(&self) -> &XPub {
        &self.pub_key
    }

    pub fn secret_key(&self) -> &XPriv {
        &self.secret_key
    }
}

#[derive(Encode, Decode, Debug, PartialEq)]
/// Hierarchical Deterministic Wallet implementation
pub struct HDWallet {
    pub version: u32,
    pub guid: [u8; 32],
    pub salt: [u8; 32],
    pub encryption_key: EncryptedEntry<[u8; 32]>,
    pub master_priv: EncryptedEntry<[u8; 32]>,
    pub internal_private_keys: EncryptedEntry<Vec<XPriv>>,
    pub external_private_keys: EncryptedEntry<Vec<XPriv>>,
    pub coloured_internal_private_keys: EncryptedEntry<HashMap<Hash160, Vec<XPriv>>>,
    pub coloured_external_private_keys: EncryptedEntry<HashMap<Hash160, Vec<XPriv>>>,
    pub external_master_xpub: XPub,
    pub external_public_keys: Vec<XPub>,
    pub internal_public_keys: Vec<XPub>,
    pub coloured_external_public_keys: HashMap<Hash160, Vec<XPub>>,
    pub coloured_internal_public_keys: HashMap<Hash160, Vec<XPub>>,
    pub external_meta: HashMap<Address, HashMap<String, String>>,
    pub internal_meta: HashMap<Address, HashMap<String, String>>,
    pub coloured_external_meta: HashMap<ColouredAddress, HashMap<String, String>>,
    pub coloured_internal_meta: HashMap<ColouredAddress, HashMap<String, String>>,
    pub txs: Vec<Transaction>,
    pub txs_meta: HashMap<Hash256, HashMap<String, String>>,
    pub outputs: Vec<Output>,
    pub outputs_meta: HashMap<Hash256, HashMap<String, String>>,
    pub outputs_witnesses_bytes: HashMap<Hash256, Vec<u8>>,
    pub scripts: HashMap<Hash256, EncryptedEntry<Script>>,
}

impl HDWallet {
    pub fn dump(&self, path: PathBuf) -> Result<(), &'static str> {
        let config = bincode::config::standard()
            .with_little_endian()
            .with_variable_int_encoding()
            .skip_fixed_array_length();
        let wallet_bytes = bincode::encode_to_vec(self, config).unwrap();

        fs::write(path, wallet_bytes).map_err(|_| "unable to dump wallet to disk")?;

        Ok(())
    }

    pub fn load(path: PathBuf) -> Result<Self, &'static str> {
        let config = bincode::config::standard()
            .with_little_endian()
            .with_variable_int_encoding()
            .skip_fixed_array_length();
        let data = fs::read(path).map_err(|_| "could not load wallet")?;
        let mut wallet: Self = bincode::decode_from_slice(&data, config)
            .map_err(|_| "corrupt wallet")?
            .0;
        wallet.init_meta();
        Ok(wallet)
    }

    pub fn assign_coinbase(&mut self, coinbase: Address) -> Result<(), &'static str> {
        match self.internal_meta.get_mut(&coinbase) {
            Some(ref mut coinbase_meta) => {
                coinbase_meta.insert("COINBASE".to_owned(), "".to_owned());
            }

            None => {
                let mut meta = HashMap::with_capacity(1);
                meta.insert("COINBASE".to_owned(), "".to_owned());
                self.internal_meta.insert(coinbase.clone(), meta);
            }
        }

        self.update_timestamp();
        Ok(())
    }

    pub fn next_coinbase(&mut self) -> Address {
        for pk in self.internal_public_keys.iter() {
            let addr = pk.to_address();

            if !self.is_coinbase(&addr) && self.tx_count(&addr) == 0 {
                self.assign_coinbase(addr.clone()).unwrap();
                self.update_timestamp();
                return addr;
            }
        }

        // Generate new batch
        for i in 0..ADDRESS_BATCH_SIZE {
            self.internal_public_keys
                .push(self.internal_public_keys.last().unwrap().derive_next());
        }

        self.next_coinbase()
    }

    pub fn tx_count(&self, address: &Address) -> u64 {
        match self.internal_meta.get(address) {
            None => 0,
            Some(meta) => match meta.get("C") {
                Some(txc) => u64::from_str_radix(txc, 16).unwrap(),
                None => 0,
            },
        }
    }

    pub fn is_coinbase(&self, address: &Address) -> bool {
        match self.internal_meta.get(address) {
            None => false,
            Some(meta) => match meta.get("COINBASE") {
                Some(_) => true,
                None => false,
            },
        }
    }

    pub fn assign_output(
        &mut self,
        out: Output,
        witness: Witness<Rsa2048, Output>,
    ) -> Result<(), &'static str> {
        let out_hash = out.hash().unwrap();

        if self.outputs_witnesses_bytes.get(out_hash).is_some() {
            return Err("output already exists");
        }

        self.outputs_witnesses_bytes
            .insert(*out_hash, witness.to_bytes());
        self.outputs.push(out);
        self.update_timestamp();

        Ok(())
    }

    pub fn assign_transaction(
        &mut self,
        tx: Transaction,
        tx_time: i64,
    ) -> Result<(), &'static str> {
        let tx_hash = tx.hash().unwrap();

        if self.txs_meta.get(tx_hash).is_some() {
            return Err("transaction already exists");
        }

        let mut meta: HashMap<String, String> = HashMap::with_capacity(1);
        meta.insert("c".to_owned(), format!("{tx_time}"));

        self.txs_meta.insert(*tx_hash, meta);
        self.txs.push(tx);
        self.update_timestamp();

        Ok(())
    }

    pub fn prune_spent_outs(&mut self) {
        unimplemented!()
    }

    fn init_meta(&mut self) {
        let zero = Hash256::zero();

        // We store the wallet meta under the zero hash key
        if self.txs_meta.get(&zero).is_some() {
            return;
        }

        let mut meta = HashMap::with_capacity(1);
        let now = Utc::now().timestamp();

        // Created at
        meta.insert("c".to_owned(), format!("{now}"));

        // Updated at
        meta.insert("u".to_owned(), format!("{now}"));

        self.txs_meta.insert(zero, meta);
    }

    fn update_timestamp(&mut self) {
        self.init_meta();
        let mut meta = self.txs_meta.get_mut(&Hash256::zero()).unwrap();
        meta.insert("u".to_owned(), format!("{}", Utc::now().timestamp()));
    }
}

pub fn dump_hdwallet(wallet: &HDWallet, wallet_name: &str) -> Result<(), &'static str> {
    #[cfg(not(test))]
    let mut wallets_path = dirs::config_dir().unwrap();

    #[cfg(test)]
    let mut wallets_path = std::env::temp_dir();

    wallets_path.push("Purplecoin");
    wallets_path.push("wallets");

    let mut wallet_path = wallets_path.clone();
    wallet_path.push(format!("{wallet_name}.dat"));

    wallet.dump(wallet_path)
}

pub fn load_hdwallet(wallet_name: &str) -> Result<HDWallet, &'static str> {
    #[cfg(not(test))]
    let mut wallets_path = dirs::config_dir().unwrap();

    #[cfg(test)]
    let mut wallets_path = std::env::temp_dir();

    wallets_path.push("Purplecoin");
    wallets_path.push("wallets");

    let mut wallet_path = wallets_path.clone();
    wallet_path.push(format!("{wallet_name}.dat"));

    HDWallet::load(wallet_path)
}

pub fn generate_hdwallet(wallet_name: &str, passphrase: &str) -> Result<HDWallet, &'static str> {
    #[cfg(not(test))]
    let mut wallets_path = dirs::config_dir().unwrap();

    #[cfg(test)]
    let mut wallets_path = std::env::temp_dir();

    wallets_path.push("Purplecoin");
    wallets_path.push("wallets");

    let mut wallet_path = wallets_path.clone();
    wallet_path.push(format!("{wallet_name}.dat"));

    if wallet_path.exists() {
        return Err("wallet already exists");
    }

    if !wallets_path.exists() {
        fs::create_dir_all(wallets_path).map_err(|_| "unable to create data dir")?;
    }

    // Generate random 64 byte seed
    let mut rng = rand::thread_rng();
    let mut seed: [u8; SEED_BYTES] = [0; SEED_BYTES];
    for i in 0..SEED_BYTES {
        seed[i] = rng.gen();
    }

    let mut encryption_key: [u8; 32] = rng.gen();
    let salt: [u8; 32] = rng.gen();

    // Calculate argon2 hash from random seed
    let mut pass_hash = argon2rs::argon2d_simple(&hex::encode(seed), &hex::encode(salt));

    // Transform argon2 hash into a 512bit output
    let mut pass_hash512 = [0; 64];
    let mut hasher = blake3::Hasher::new();
    hasher.update(&pass_hash);
    let mut out = hasher.finalize_xof();
    out.fill(&mut pass_hash512);

    let chain_code = &pass_hash512[32..];
    let mut master_priv_key = [0; 32];
    master_priv_key.copy_from_slice(&pass_hash512[..32]);

    // Calculate external and internal priv keys by transforming
    // the master priv key to a 512 bit output.
    let mut master_priv_hash512 = [0; 64];
    let mut hasher = blake3::Hasher::new();
    hasher.update(&master_priv_key);
    hasher.update(&[0x00]);
    let mut out = hasher.finalize_xof();
    out.fill(&mut master_priv_hash512);

    let master_internal_priv_key = &master_priv_hash512[..32];
    let master_external_priv_key = &master_priv_hash512[32..];

    // Calculate passphrase argon2 hash
    let mut passphrase_hash = argon2rs::argon2d_simple(passphrase, &hex::encode(salt));
    let mut passphrase_hash256 = [0; 32];
    let mut hasher = blake3::Hasher::new();
    hasher.update(&passphrase_hash);
    let mut out = hasher.finalize_xof();
    out.fill(&mut passphrase_hash256);

    let mut internal_public_keys = vec![];
    let mut internal_private_keys = vec![];
    let mut external_public_keys = vec![];
    let mut external_private_keys = vec![];

    let mut master_keypair_internal = XKeypair::new_master(
        master_internal_priv_key,
        chain_code,
        [0, 0, 0, 0],
        0x00,
        0x000000,
    );
    let mut master_keypair_external = XKeypair::new_master(
        master_external_priv_key,
        chain_code,
        [0, 0, 0, 0],
        0x00,
        0x000000,
    );

    // Pre-generate keypairs
    for i in 0..ADDRESS_BATCH_SIZE {
        if i == 0 {
            let mut next_internal = master_keypair_internal.derive_next();
            let mut next_external = master_keypair_external.derive_next();
            internal_public_keys.push(next_internal.pub_key().clone());
            internal_private_keys.push(next_internal.secret_key().clone());
            external_public_keys.push(next_external.pub_key().clone());
            external_private_keys.push(next_external.secret_key().clone());
            next_internal.zeroize();
            next_external.zeroize();
            continue;
        }
        internal_public_keys.push(internal_public_keys.last().unwrap().derive_next());
        internal_private_keys.push(internal_private_keys.last().unwrap().derive_next());
        external_public_keys.push(external_public_keys.last().unwrap().derive_next());
        external_private_keys.push(external_private_keys.last().unwrap().derive_next());
    }

    let mut wallet = HDWallet {
        version: 1,
        salt,
        guid: rng.gen(),
        external_master_xpub: master_keypair_external.pub_key().clone(),
        encryption_key: EncryptedEntry::xchacha20poly1305(&passphrase_hash256, encryption_key)?,
        master_priv: EncryptedEntry::xchacha20poly1305(&encryption_key, master_priv_key)?,
        internal_private_keys: EncryptedEntry::xchacha20poly1305(
            &encryption_key,
            internal_private_keys,
        )?,
        external_private_keys: EncryptedEntry::xchacha20poly1305(
            &encryption_key,
            external_private_keys,
        )?,
        coloured_internal_private_keys: EncryptedEntry::xchacha20poly1305(
            &encryption_key,
            HashMap::new(),
        )?,
        coloured_external_private_keys: EncryptedEntry::xchacha20poly1305(
            &encryption_key,
            HashMap::new(),
        )?,
        internal_public_keys,
        external_public_keys,
        coloured_internal_public_keys: HashMap::new(),
        coloured_external_public_keys: HashMap::new(),
        external_meta: HashMap::new(),
        internal_meta: HashMap::new(),
        coloured_external_meta: HashMap::new(),
        coloured_internal_meta: HashMap::new(),
        txs: vec![],
        txs_meta: HashMap::new(),
        outputs: vec![],
        outputs_meta: HashMap::new(),
        outputs_witnesses_bytes: HashMap::new(),
        scripts: HashMap::new(),
    };
    wallet.init_meta();

    seed.zeroize();
    encryption_key.zeroize();
    pass_hash.zeroize();
    pass_hash512.zeroize();
    passphrase_hash.zeroize();
    passphrase_hash256.zeroize();
    master_priv_hash512.zeroize();
    master_keypair_external.zeroize();
    master_keypair_internal.zeroize();

    // Write hdwallet to disk
    fs::File::create(wallet_path.clone()).map_err(|_| "unable to dump wallet to disk")?;
    wallet.dump(wallet_path)?;

    Ok(wallet)
}

#[cfg(test)]
mod tests {
    use super::*;

    // Wallet names must be unique in tests
    fn generate_wallet_name() -> String {
        let mut rng = rand::thread_rng();
        let bytes: [u8; 32] = rng.gen();
        hex::encode(bytes)
    }

    #[test]
    fn hdwallet_generate_then_load() {
        let wallet_name = generate_wallet_name();
        let wallet = generate_hdwallet(&wallet_name, "test").unwrap();
        let loaded_wallet = load_hdwallet(&wallet_name).unwrap();
        assert_eq!(wallet, loaded_wallet);
    }

    #[test]
    fn hdwallet_generate_dump_then_load() {
        let wallet_name = generate_wallet_name();
        let wallet = generate_hdwallet(&wallet_name, "test").unwrap();
        dump_hdwallet(&wallet, &wallet_name).unwrap();
        let loaded_wallet = load_hdwallet(&wallet_name).unwrap();
        assert_eq!(wallet, loaded_wallet);
    }

    // #[test]
    // fn sign_transaction() {

    // }
}
