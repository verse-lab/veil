
namespace Veil

/-- Returns true when running in the online environment. -/
def isVeilOnlineEnv : IO Bool := do
  return (← IO.getEnv "VEIL_ONLINE_ENV").isSome

def getNumCores : IO Nat := do
  -- A malformed value must not yield 0: `toNat!` panics *and continues with 0*,
  -- which would make the VC manager's `.startAll` start zero tasks and wedge
  -- awaiting commands with no exception anywhere. Parse defensively, floor at 1.
  -- First check if LEAN_NUM_THREADS is set (controls the Lean runtime thread pool)
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

end Veil
