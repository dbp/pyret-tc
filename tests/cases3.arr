#lang pyret

#! branch bar in the cases expression is not a valid variant of the data type Foo

data Foo:
  | foo
end

data Bar:
  | bar
end

cases(Foo) foo:
  | foo => 1
  | bar => 2
end