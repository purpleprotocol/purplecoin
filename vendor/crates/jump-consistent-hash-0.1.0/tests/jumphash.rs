extern crate jump_consistent_hash;
use jump_consistent_hash::hash;

struct Test {
    key: u64,
    len: Vec<u32>,
}

#[test]
#[cfg_attr(rustfmt, rustfmt_skip)]
fn table_test() {
    let tests = vec![
        Test {
            key: 0,
            len: vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        },
        Test {
            key: 1,
            len: vec![0, 0, 0, 0, 0, 0, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 17, 17],
        },
        Test {
            key: 0xdeadbeef,
            len: vec![0, 1, 2, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 16, 16, 16],
        },
        Test {
            key: 0x0ddc0ffeebadf00d,
            len: vec![0, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 15, 15, 15, 15],
        }
    ];
    for test in tests {
        for (i, len) in test.len.iter().enumerate() {
            let got = hash(test.key, i + 1);
            assert_eq!(got, *len);
        }
    }
}

#[test]
fn hash_test() {
    assert_eq!(6, hash(10863919174838991, 11));
    assert_eq!(3, hash(2016238256797177309, 11));
    assert_eq!(5, hash(1673758223894951030, 11));
    assert_eq!(80343, hash(2, 100001));
    assert_eq!(22152, hash(2201, 100001));
    assert_eq!(15018, hash(2202, 100001));
}
