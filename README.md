# Optimal Arrays

## Overview

This Rust crate implements a resizable array as described in the paper **Resizable Arrays in Optimal Time and Space** by Andrej Brodnik et. al., published in 1999.

* Online ISBN 978-3-540-48447-9
* https://doi.org/10.1137/23M1575792

This data structure supports `push` and `pop` operations and does _not_ support inserts or removes at other locations within the array. One exception is the `swap/remove` operation (similar to the `DeleteRandom` operation described in the paper) which will retrieve a value from a specified index, overwrite that slot with the value at the end of the array, decrement the count, and return the retrieved value.

### Memory Usage

Compared to the `Vec` type in the Rust standard library, this data structure will have substantially less unused space, on the order of O(√N). The index block contributes to the overhead of this data structure, and that is on the order of O(√N). Based on the current implementation of `Vec`, as much as 50% of the space may be unused since it has a growth factor of 2. The [Segment Array]((https://github.com/nlfiedler/segarray)) has the same growth factor as `Vec` and potentially the same proportion of unused space (its index block is a fixed size).

## Examples

A simple example copied from the unit tests.

```rust
let inputs = [
    "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
];
let mut arr: OptimalArray<String> = OptimalArray::new();
for item in inputs {
    arr.push(item.to_owned());
}
for (idx, elem) in arr.iter().enumerate() {
    assert_eq!(inputs[idx], elem);
}
```

## Supported Rust Versions

The Rust edition is set to `2024` and hence version `1.85.0` is the minimum supported version.

## Troubleshooting

### Memory Leaks

Finding memory leaks with [Address Sanitizer](https://clang.llvm.org/docs/AddressSanitizer.html) is fairly [easy](https://doc.rust-lang.org/beta/unstable-book/compiler-flags/sanitizer.html) and seems to work best on Linux. The shell script below gives a quick demonstration of running one of the examples with ASAN analysis enabled.

```shell
#!/bin/sh
env RUSTDOCFLAGS=-Zsanitizer=address RUSTFLAGS=-Zsanitizer=address \
    cargo run -Zbuild-std --target x86_64-unknown-linux-gnu --release --example leak_test
```

## References

* \[1\]: [Resizable Arrays in Optimal Time and Space (1999)](https://dl.acm.org/doi/10.5555/645932.673194)
