//
// Copyright (c) 2025 Nathan Fiedler
//
use optarray::OptimalArray;

//
// Create and drop collections and iterators in order to test for memory leaks.
// Must allocate Strings in order to fully test the drop implementation.
//
fn main() {
    // add only enough values to allocate one segment
    let mut array: OptimalArray<String> = OptimalArray::new();
    let value = ulid::Ulid::new().to_string();
    array.push(value);

    // add enough values to allocate a few segments
    let mut array: OptimalArray<String> = OptimalArray::new();
    for _ in 0..12 {
        let value = ulid::Ulid::new().to_string();
        array.push(value);
    }

    // push a bunch, pop a few, push more to test Grow/Shrink handling of the
    // extra empty data block
    let mut array: OptimalArray<u64> = OptimalArray::new();
    for value in 0..35 {
        array.push(value);
    }
    for _ in 0..10 {
        array.pop();
    }
    for value in 0..12 {
        array.push(value);
    }

    // test pushing many elements then popping all of them
    let mut array: OptimalArray<String> = OptimalArray::new();
    for _ in 0..512 {
        let value = ulid::Ulid::new().to_string();
        array.push(value);
    }
    while !array.is_empty() {
        array.pop();
    }

    // IntoIterator: add only enough values to allocate one segment
    let mut array: OptimalArray<String> = OptimalArray::new();
    let value = ulid::Ulid::new().to_string();
    array.push(value);
    let _ = array.into_iter();

    // IntoIterator: add enough values to allocate a bunch of segments
    let mut array: OptimalArray<String> = OptimalArray::new();
    for _ in 0..250 {
        let value = ulid::Ulid::new().to_string();
        array.push(value);
    }
    // skip enough elements to pass over a few segments then drop
    for (index, value) in array.into_iter().skip(28).enumerate() {
        if index == 28 {
            println!("28: {value}");
            // exit the iterator early intentionally
            break;
        }
    }
}
