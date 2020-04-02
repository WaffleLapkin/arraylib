## 0.2.0

- Add `Slice::array_windows` method and `iter::ArrayWindows` iterator (https://github.com/WaffleLapkin/arraylib/pull/16)
- Add `if_alloc` macro (https://github.com/WaffleLapkin/arraylib/pull/13, https://github.com/WaffleLapkin/arraylib/pull/15)
- Rename `Array::{from_iter => try_from_iter}` and add `Array::from_iter` (https://github.com/WaffleLapkin/arraylib/pull/12)
- Add `ArrayExt::{ref,mut}_cast`, `ArrayExt::try_{ref,mut}_cast` and `ArrayExt::{ref,mut}_cast_unchecked` methods (https://github.com/WaffleLapkin/arraylib/pull/9) 
- Clean `util::init::try_unfold_array` and fix UB in it (see issue https://github.com/WaffleLapkin/arraylib/issues/5 and PRs https://github.com/WaffleLapkin/arraylib/pull/7, https://github.com/WaffleLapkin/arraylib/pull/10)
- Simplify `SizeError` (https://github.com/WaffleLapkin/arraylib/pull/4 and https://github.com/WaffleLapkin/arraylib/pull/17)

## 0.1.0 

Initial version (commit https://github.com/WaffleLapkin/arraylib/commit/1e5d034c37ff7a182c0462d6c41d4f2c74cf20f6)
