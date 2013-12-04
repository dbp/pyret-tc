#lang pyret

#! Data type in cases expression is not well formed. Was Option<Number, String>, but should have been of form Option<T>.

cases(Option<Number, String>) none:
  | else => 1
end