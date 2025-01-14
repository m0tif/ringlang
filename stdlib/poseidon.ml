(T)

static ROUNDS_F = 10
static ROUNDS_P = 20

signal state: [T]

loop ROUNDS_F / 2 {
  
}

signal x = 0
signal z = 100

signal y = x + z

if z == y {
  return 0
} else {
  return 1
}

