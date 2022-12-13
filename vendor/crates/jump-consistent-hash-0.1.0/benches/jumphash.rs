#![feature(test)]
extern crate test;
extern crate jump_consistent_hash as ch;

use test::Bencher;

#[bench]
fn bench_2201_100001(b: &mut Bencher) {
    b.iter(|| test::black_box(ch::hash(2201, 100001)));
}

#[bench]
fn bench_10863919174838991_11(b: &mut Bencher) {
    b.iter(|| test::black_box(ch::hash(10863919174838991, 11)));
}
