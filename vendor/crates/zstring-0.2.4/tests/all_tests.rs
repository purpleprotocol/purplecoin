use zstring::CharDecoder;

#[test]
fn bstr_example() {
  let bytes = *b"a\xF0\x9F\x87z";
  let chars: Vec<char> = CharDecoder::from(bytes.iter().copied()).collect();
  assert_eq!(vec!['a', '\u{FFFD}', 'z'], chars);
}

#[test]
fn fuzz_found_data() {
  use bstr::ByteSlice;

  let bytes = [0b11110101, 0b10101111];

  let s_lossy = String::from_utf8_lossy(&bytes);
  let s_bstr = bytes.chars().collect::<String>();
  assert_eq!(s_lossy, s_bstr); // passes, they agree

  let s_decoded = CharDecoder::from(bytes.iter().copied()).collect::<String>();
  assert_eq!(s_lossy, s_decoded);

  // Note: Other byte sequences will still fail!
}
