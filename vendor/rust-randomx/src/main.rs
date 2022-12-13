use num_cpus;
use rand::prelude::*;
use rust_randomx::{Context, Difficulty, Hasher};
use std::thread;
use triomphe::Arc;

fn main() {
    let context = Arc::new(Context::new(b"RandomX key", true));

    let num_threads = num_cpus::get();
    let mut threads = Vec::new();
    for _ in 0..num_threads {
        let context = Arc::clone(&context);
        let diff = Difficulty::new(0x027fffff); // 0x00007fff ff000000 ... 00000000
        threads.push(thread::spawn(move || {
            let mut rng = rand::thread_rng();
            let mut hasher = Hasher::new(context);
            let mut nonce: u32 = rng.gen();
            hasher.hash_first(&nonce.to_le_bytes());
            loop {
                let next_nonce: u32 = rng.gen();
                let out = hasher.hash_next(&next_nonce.to_le_bytes());
                if out.meets_difficulty(diff) {
                    println!("{} -> {:?}", nonce, out);
                }
                nonce = next_nonce;
            }
        }));
    }

    for t in threads {
        t.join().unwrap();
    }
}
