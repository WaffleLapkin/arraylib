# arraylib
[![CI status](https://github.com/WaffleLapkin/arraylib/workflows/Continuous%20integration/badge.svg)](https://github.com/WaffleLapkin/arraylib/actions)
[![Telegram](https://img.shields.io/badge/tg-WaffleLapkin-9cf?logo=telegram)](https://vee.gg/t/WaffleLapkin)
[![crates.io](https://img.shields.io/crates/v/arraylib.svg)](https://crates.io/crates/arraylib)
[![documentation (docs.rs)](https://docs.rs/arraylib/badge.svg)](https://docs.rs/arraylib)
[![documentation (master)](https://img.shields.io/badge/docs-master-blue)](https://arraylib.netlify.com/arraylib)
[![LICENSE](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

`arraylib` provides tools for working with arrays. See [docs](https://docs.rs/arraylib) for more.  

```toml
[dependencies]
arraylib = "0.3"
```

_Compiler support: requires rustc 1.41+_

## Examples

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
