import Lean

namespace Veil

/-- Returns true when running in the online environment. -/
def isVeilOnlineEnv : IO Bool := do
  return (← IO.getEnv "VEIL_ONLINE_ENV").isSome

/-- Detect the number of cores: `LEAN_NUM_THREADS` if set (this is what sizes
the Lean task pool), otherwise platform-specific detection. -/
private def detectNumCores : IO Nat := do
  if let some n := (← IO.getEnv "LEAN_NUM_THREADS") then
    if let some k := n.toNat? then
      return max 1 k
  -- Otherwise (also on a malformed value), use platform-specific detection
  if System.Platform.isWindows then
    let val ← IO.getEnv "NUMBER_OF_PROCESSORS"
    return max 1 (val.bind String.toNat? |>.getD 1)
  else
    -- Linux and other Unix-like systems (POSIX compliant)
    let output ← IO.Process.output { cmd := "getconf", args := #["_NPROCESSORS_ONLN"] }
    return max 1 (output.stdout.trimAscii.toNat?.getD 1)

initialize numCoresCache : IO.Ref (Option Nat) ← IO.mkRef none

/-- Number of cores available to this process, memoized. This must be cheap and
never throw. On detection failure this falls back to 1 (slow but safe). -/
def getNumCores : BaseIO Nat := do
  if let some n := ← numCoresCache.get then
    return n
  let n ← EIO.catchExceptions detectNumCores fun _ => pure 1
  numCoresCache.set (some n)
  return n

end Veil
