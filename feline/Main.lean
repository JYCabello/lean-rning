
def bufsize : USize := 20 * 1024

partial def dump (stream: IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream

def fileStream (filename: System.FilePath) : IO (Option IO.FS.Stream) := do
  if (not (← filename.pathExists)) then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))


def main : IO Unit :=
  IO.println s!"Hello, cats!"
