
def bufsize : USize := 20 * 1024

partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream

def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  if (not (← filename.pathExists)) then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))

def stringStream (message: String) : IO IO.FS.Stream := do
  let bytes := message.toUTF8
  let ref ← IO.mkRef bytes
  pure
    { read := fun n => do
        let buf ← ref.get
        if buf.isEmpty then
          pure ByteArray.empty
        else
          let take := if buf.size < n.toNat then buf.size else n.toNat
          let chunk := buf.extract 0 take
          ref.set (buf.extract take buf.size)
          pure chunk
      flush := pure ()
      write := λ _ => pure ()
      getLine := do
        let buf ← ref.get
        if buf.isEmpty then
          pure ""
        else
          let rec findNewline (i : Nat) : Option Nat :=
            if h : i >= buf.size then
              none
            else if buf.get i == 10 then
              some i
            else
              findNewline (i + 1)
          match findNewline 0 with
          | some pos =>
            let lineBytes := buf.extract 0 pos
            ref.set (buf.extract (pos + 1) buf.size)
            match String.fromUTF8? lineBytes with
            | some s => pure s
            | none => pure ""
          | none =>
            ref.set ByteArray.empty
            match String.fromUTF8? buf with
            | some s => pure s
            | none => pure ""
      putStr := λ _ => pure ()
      isTty := pure true }

def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with
  | [] => pure exitCode
  | "--help" :: args =>
    dump (← stringStream "no help is coming")
    process exitCode args
  | "-" :: args =>
    dump (← IO.getStdin)
    process exitCode args
  | filename :: args =>
    match ← fileStream ⟨filename⟩ with
    | none => process 1 args
    | some stream =>
      dump stream
      process exitCode args

def main (args : List String) : IO UInt32 :=
  match args with
  | [] => process 0 ["-"]
  | _ =>  process 0 args
