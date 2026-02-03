
namespace Veil

def getNumCores : IO Nat := do
  -- First check if LEAN_NUM_THREADS is set (controls the Lean runtime thread pool)
  if let some n := (← IO.getEnv "LEAN_NUM_THREADS") then
    return n.toNat!
  -- Otherwise, use platform-specific detection
  if System.Platform.isWindows then
    let val ← IO.getEnv "NUMBER_OF_PROCESSORS"
    return val.map String.toNat! |>.getD 1
  else
    -- Linux and other Unix-like systems (POSIX compliant)
    let output ← IO.Process.output { cmd := "getconf", args := #["_NPROCESSORS_ONLN"] }
    return output.stdout.trimAscii.toNat!

end Veil
