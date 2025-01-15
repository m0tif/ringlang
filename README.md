# mathlang

A runtime agnostic language for expressing cryptographic programs.

## poseidon

- [x] `static` variables (compile time only)
- [x] `static` scalars, vectors, and matrices
- [x] `signal` variables
- [x] basic math operations
- [x] indexed read/write for variables
- [x] vector/matrix/hypercube literals
- [ ] `loop` and `if` flow control using `static` variables
- [ ] function calls
- [ ] floored division (`/`) for statics

## good to have

- [ ] macro for determining shape of a variable (returns a `static`)
- [ ] macro for field prime assertion (functions halt compilation if they're use in the wrong field)
