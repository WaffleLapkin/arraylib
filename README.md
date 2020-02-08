# arraylib
[![CI status](https://github.com/WaffleLapkin/arraylib/workflows/Continuous%20integration/badge.svg)](https://github.com/WaffleLapkin/arraylib/actions)
[![Telegram](https://img.shields.io/badge/tg-WaffleLapkin-9cf?logo=telegram)](https://vee.gg/t/WaffleLapkin)
[![docs.rs](https://img.shields.io/badge/docs.rs-arraylib-blue.svg)](https://docs.rs/arraylib)
[![LICENSE](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)
[![crates.io](https://img.shields.io/badge/crates.io-v0.1.0-orange.svg)](https://crates.io/crates/arraylib)

Tools for working with arrays. E.g.:

```rust
use arraylib::{Array, ArrayMap, ArrayExt};
// Array creation
let arr = <[_; 11]>::unfold(1, |it| {
    let res = *it;
    *it *= -2;
    res
});

// Mapping
let arr = arr.map(|it| it * 2);
assert_eq!(arr, [2, -4, 8, -16, 32, -64, 128, -256, 512, -1024, 2048]);

// By-value iterator
arr.iter_move().for_each(|i: i32| {})
```
