# Green-jet energy factor and canonical graph closure

This note is a construction ledger for the passage from the exact Green-jet
moment relation to a closed operator.  It records provenance; it does not add
an external spectral input.

## 1. Algebraic data

Write `e_n` and `o_n` for the even and odd Green jets.  The Gram
representation gives

```text
<e_i,e_j> = h_(i+j),
<o_i,o_j> = h_(i+j+1),
<e_i,o_j> = 0.
```

Let `E_0` and `O_0` be their algebraic spans inside the corresponding closed
parity sectors.  Define the two algebraic partial operators

```text
B_0 e_n = o_n,
C_0 o_n = e_(n+1).
```

Linear independence makes these prescriptions well defined on the chosen
bases.  By construction, `E_0` and `O_0` are dense in their closed sectors.

## 2. The shifted moment is the adjoint law

On generators, the same shifted moment is read in two ways:

```text
<B_0 e_i,o_j>
  = <o_i,o_j>
  = h_(i+j+1)
  = <e_i,e_(j+1)>
  = <e_i,C_0 o_j>.
```

Bilinearity and the two algebraic bases extend this equality to every
`x in E_0` and `y in O_0`:

```text
<B_0 x,y> = <x,C_0 y>.
```

Thus `C_0` is a densely defined formal adjoint for `B_0`.  This relation is
derived before any closure is introduced.

## 3. Why the graph closure is an operator

Suppose `(0,v)` belongs to the topological closure of the graph of `B_0`.
For every `z` in the domain of `C_0`, the formal-adjoint identity defines a
closed annihilator containing the graph.  It therefore also contains its
closure, and hence

```text
<v,z> = <0,C_0 z> = 0.
```

The domain of `C_0` is dense in the odd sector, so `v = 0`.  Therefore the
closed graph has no nonzero vertical vector and is the graph of a unique
partial linear operator.  In Lean this proves

```text
B_0.IsClosable.
```

Its graph closure is denoted by `closedGreenJetEnergyFactor`.  The formalized
consequences are

```text
B_0 <= closedGreenJetEnergyFactor,
closedGreenJetEnergyFactor.IsClosed,
closedGreenJetEnergyFactor.HasCore E_0.
```

No completeness hypothesis is needed for the closability argument itself;
the result remains valid when the construction is subsequently placed in the
canonical completed Hilbert carrier.

## 4. Closure is not circularity

Being closed is an analytic property of the final graph.  Circularity would
occur only if that closedness were used to establish one of its own inputs,
such as the shifted-moment identity, the formal-adjoint law, or density of the
reverse-shift domain.  The dependency order here is instead

```text
Green Gram relation
  -> shifted-moment identity
  -> formal-adjoint identity on dense algebraic cores
  -> vertical-kernel argument for the graph closure
  -> canonical closed factor.
```

The provenance firewalls distinguish these layers; they do not make
closedness suspicious and they are not additional hypotheses in this chain.

The positive operator associated with the factor, customarily written
`B_bar^* B_bar`, and its self-adjointness are the next layer.  They are not
claimed by the present file.
