import Veil

veil module FieldNamedNone

type value
individual none : value

#gen_state

#guard_msgs in
after_init {
  none := *
}

end FieldNamedNone


veil module FieldNamedNone₂

type value
individual none : value
relation r (n : value) (m : value)

#gen_state

#guard_msgs in
after_init {
  none := *
  r := *
}

end FieldNamedNone₂
