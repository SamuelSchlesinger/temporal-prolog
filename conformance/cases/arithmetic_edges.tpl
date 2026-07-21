% Portable integer spellings and signed floor-division semantics.
Q1 is -7 div 3 => quotient_negative(Q1).
R1 is -7 mod 3 => remainder_negative(R1).
Q2 is 7 div -3 => quotient_negative_divisor(Q2).
R2 is 7 mod -3 => remainder_negative_divisor(R2).
P is 2 + 3 * 4 div 5 => precedence(P).
Huge is 9223372036854775808 * 9223372036854775808
  => arbitrary_precision(Huge).
Bad is 1 div 0 => division_by_zero_succeeded(Bad).
canonical_integer_spellings(007, -0).
