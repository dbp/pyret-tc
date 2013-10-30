#lang pyret

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