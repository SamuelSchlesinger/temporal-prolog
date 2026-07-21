% Pattern functions require their input positions to be grounded before use.
identity(X) -> X.
identity(X) = Y => leaked(X, Y).
