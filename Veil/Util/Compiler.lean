module

public import Lean.CoreM
import all Lean.Compiler.LCNF.Specialize

namespace Veil.ModelChecker.Compilation

/-- Keep specialization reuse within the native imports selected for execution.
Lean can otherwise reuse a generic helper from an unrelated verification module,
such as a list formatter specialized while compiling an SMT configuration type.
The cache is compiler-internal, so access is confined to this module. -/
public def restrictSpecializationCache (imports : Array Lean.Name) : Lean.CoreM Unit := do
  let env ← Lean.getEnv
  let allowed := imports.foldl (fun names name => names.insert name) ({} : Lean.NameSet)
  let cache := Lean.Compiler.LCNF.Specialize.specCacheExt.getState env
  let cache := cache.fold (init := ({} : Lean.Compiler.LCNF.Specialize.Cache)) fun kept key name =>
    let retain := match env.getModuleIdxFor? name with
      | none => true
      | some idx => allowed.contains env.header.modules[idx]!.module
    if retain then kept.insert key name else kept
  Lean.modifyEnv (Lean.Compiler.LCNF.Specialize.specCacheExt.setState · cache.switch)

end Veil.ModelChecker.Compilation
