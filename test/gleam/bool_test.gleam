import gleam/bool
import gleam/order
import gleam/should

pub fn negate_test() {
  bool.negate(True)
  |> should.be_false

  bool.negate(False)
  |> should.be_true
}

pub fn nor_test() {
  bool.nor(False, False)
  |> should.be_true

  bool.nor(False, True)
  |> should.be_false

  bool.nor(True, False)
  |> should.be_false

  bool.nor(True, True)
  |> should.be_false
}

pub fn nand_test() {
  bool.nand(False, False)
  |> should.be_true

  bool.nand(False, True)
  |> should.be_true

  bool.nand(True, False)
  |> should.be_true

  bool.nand(True, True)
  |> should.be_false
}

pub fn exclusive_or_test() {
  bool.exclusive_or(True, True)
  |> should.be_false

  bool.exclusive_or(False, False)
  |> should.be_false

  bool.exclusive_or(True, False)
  |> should.be_true

  bool.exclusive_or(False, True)
  |> should.be_true
}

pub fn exclusive_nor_test() {
  bool.exclusive_nor(False, False)
  |> should.be_true

  bool.exclusive_nor(False, True)
  |> should.be_false

  bool.exclusive_nor(True, False)
  |> should.be_false

  bool.exclusive_nor(True, True)
  |> should.be_true
}

pub fn compare_test() {
  bool.compare(True, True)
  |> should.equal(order.Eq)

  bool.compare(True, False)
  |> should.equal(order.Gt)

  bool.compare(False, False)
  |> should.equal(order.Eq)

  bool.compare(False, True)
  |> should.equal(order.Lt)
}

pub fn max_test() {
  bool.max(True, True)
  |> should.be_true

  bool.max(True, False)
  |> should.be_true

  bool.max(False, False)
  |> should.be_false

  bool.max(False, True)
  |> should.be_true
}

pub fn min_test() {
  bool.min(True, True)
  |> should.be_true

  bool.min(True, False)
  |> should.be_false

  bool.min(False, False)
  |> should.be_false

  bool.min(False, True)
  |> should.be_false
}

pub fn to_int_test() {
  bool.to_int(True)
  |> should.equal(1)

  bool.to_int(False)
  |> should.equal(0)
}

pub fn to_string_test() {
  bool.to_string(True)
  |> should.equal("True")

  bool.to_string(False)
  |> should.equal("False")
}

pub fn guard_test() {
  let assert 2 = {
    use <- bool.guard(when: True, return: 2)
    1
  }

  let assert 1 = {
    use <- bool.guard(when: False, return: 2)
    1
  }
}

pub fn lazy_guard_test() {
  let oops = fn() { panic as "this shouldn't run!" }

  let assert 2 = {
    use <- bool.lazy_guard(when: True, otherwise: oops)
    2
  }

  let assert 1 = {
    use <- bool.lazy_guard(when: False, return: oops)
    1
  }
}
