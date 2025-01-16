# all arguments to entrypoint are comp
(T)

comp ROUNDS_F = 10 # POSEIDON_F(T)
comp ROUNDS_P = 20 # POSEIDON_P(T)
comp C: [T] # POSEIDON constants
comp M: [T][T] # POSEIDON matrices

signal state: [T]

# current round index
comp r = 0

# first set of full rounds
for _ in 0..ROUNDS_F \ 2 {
    linear_layer!
    pow5(state)
    mix_full!
    r = r + 1
}

# partial rounds
for _ in 0..ROUNDS_P {
    linear_layer!
    state[0] = pow5(state[0])
    mix_full!
    r = r + 1
}

# final set of full rounds
for _ in 0..ROUNDS_F \ 2 {
    linear_layer!
    state = pow5(state)
    mix_full!
    r = r + 1
}

return state

macro linear_layer {
    # assert_comp_scalar!(T)
    for x in 0..T {
        state[x] = state[x] + C[r * T + x]
    }
}

macro mix_full {
    signal out: [T]
    for x in 0..T {
        # M[x] is a vector of T elements
        out[x] = sum(M[x] * state)
    }
    state = out
}
