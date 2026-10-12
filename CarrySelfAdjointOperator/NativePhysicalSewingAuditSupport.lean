import Lean

open Lean Elab Command

/-- Public declarations are checked through types and bodies, with the
same foundational allowance as the existing repository audit. -/
elab "#audit_physical_sewing " ids:ident+ : command => do
  let env := (← getEnv).setExporting false
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut todo : List Name := []
  let mut roots : Nat := 0
  for id in ids do
    let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    todo := decl :: todo
    roots := roots + 1
    let deps ← collectAxioms decl
    for name in deps do
      unless allowed.contains name do
        throwError "Unexpected foundational dependency: {decl} depends on {name}"
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if !seen.contains name then
      seen := seen.insert name
      if name == `sorryAx then
        throwError "Unverified dependency: {name}"
      if let some info := env.find? name then
        for dependency in info.type.getUsedConstants do
          todo := dependency :: todo
        if let some value := info.value? then
          for dependency in value.getUsedConstants do
            todo := dependency :: todo
  logInfo m!"Physical sewing public roots: {roots}; type/body dependency closure: {seen.size}; foundational guard passed"
