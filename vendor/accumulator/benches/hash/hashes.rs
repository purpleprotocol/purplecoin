/// See https://bheisler.github.io/criterion.rs/book/getting_started.html to add more benchmarks.
#[macro_use]
extern crate criterion;

use accumulator::hash::{hash, hash_to_prime, hash_to_prime_with_counter};
use criterion::Criterion;
use rand::Rng;
use rayon::prelude::*;

fn bench_hash_to_prime(random_bytes: [u8; 32]) {
    hash_to_prime(&random_bytes);
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("hash_blake3", |b| {
        let random_bytes = rand::thread_rng().gen::<[u8; 32]>();
        b.iter(|| hash(&random_bytes));
    });

    c.bench_function("hash_to_prime", |b| {
        let random_bytes = rand::thread_rng().gen::<[u8; 32]>();
        b.iter(|| bench_hash_to_prime(random_bytes))
    });
    c.bench_function("hash_to_prime_with_counter", |b| {
        let random_bytes = rand::thread_rng().gen::<[u8; 32]>();
        let (prime, counters) = hash_to_prime_with_counter(&random_bytes, None);
        b.iter(|| hash_to_prime_with_counter(&random_bytes, Some(counters)))
    });

    for batch_size in vec![100, 500, 1000, 3000] {
        c.bench_function(&format!("hash_to_prime_batch_{}", batch_size), |b| {
            let batch: Vec<_> = (0..batch_size)
                .into_iter()
                .map(|_| rand::thread_rng().gen::<[u8; 32]>())
                .collect();
            b.iter(|| {
                batch
                    .par_iter()
                    .map(|b| bench_hash_to_prime(*b))
                    .collect::<Vec<_>>()
            })
        });

        c.bench_function(
            &format!("hash_to_prime_with_counter_batch_{}", batch_size),
            |b| {
                let batch: Vec<_> = (0..batch_size)
                    .into_iter()
                    .map(|_| {
                        let b = rand::thread_rng().gen::<[u8; 32]>();
                        let (_prime, counters) = hash_to_prime_with_counter(&b, None);
                        (b, counters)
                    })
                    .collect();
                b.iter(|| {
                    batch
                        .par_iter()
                        .map(|(b, counters)| hash_to_prime_with_counter(&b, Some(*counters)))
                        .collect::<Vec<_>>()
                })
            },
        );
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
