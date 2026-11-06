module

public import Veil

/-! What the VS Code extension (`editors/vscode`) relies on, by name and by format; its own tests
cover the rest of `Veil.ideProtocolVersion`, such as the output of binaries. If this test fails,
the change may break the extension: see "Changing what the extension relies on" in
`editors/vscode/PUBLISHING.md`. -/

open Lean Veil

/-- info: 1 -/
#guard_msgs in
#eval ideProtocolVersion

/-! The kinds of the code actions that the extension asks Lean for, with their commands -/

/--
info: [("refactor.veil.ideProtocol", "veil.ideProtocol"),
  ("refactor.veil.executableModules", "veil.modelCheck.executableModules"),
  ("refactor.veil.modelCheckConfig", "veil.modelCheck.createConfig"),
  ("refactor.veil.modelCheckSources", "veil.modelCheck.sources")]
-/
#guard_msgs in
#eval [(ideProtocolKind, ideProtocolCommand), (executableModulesKind, executableModulesCommand),
  (configTemplateKind, configTemplateCommand), (moduleSourcesKind, moduleSourcesCommand)]

/-- info: "Model checker built: " -/
#guard_msgs in
#eval ExecutionWorkflow.builtMessagePrefix

/-! The JSON of what the code actions give and of what binaries report when they start -/

/-- info: {"actionLabels":["send","recv"],"ideProtocol":1} -/
#guard_msgs in
#eval IO.println (toJson ({ actionLabels := ["send", "recv"] } : ModelChecker.Compilation.StartReport)).compress

/--
info: {"import":"MyProject.Paxos","instantiation":[{"name":"node","value":"_"}],"module":"Paxos","theory":[{"name":"limit","value":"_"}]}
-/
#guard_msgs in
#eval IO.println (toJson ({
  «module» := "Paxos", «import» := some "MyProject.Paxos",
  instantiation := #[{ name := "node", value := "_" }], «theory» := #[{ name := "limit", value := "_" }] }
  : ConfigTemplate)).compress

/-- info: {"import":null,"instantiation":[],"module":"Paxos","theory":[]} -/
#guard_msgs in
#eval IO.println (toJson ({ «module» := "Paxos", «import» := none, instantiation := #[], «theory» := #[] }
  : ConfigTemplate)).compress

/--
info: {"actions":[{"character":0,"file":"/project/Paxos.lean","line":12,"name":"send"}],"properties":[{"character":2,"file":"/project/Paxos.lean","line":30,"name":"agreement"}]}
-/
#guard_msgs in
#eval IO.println (toJson ({
  «actions» := #[{ name := "send", file := "/project/Paxos.lean", line := 12, character := 0 }],
  «properties» := #[{ name := "agreement", file := "/project/Paxos.lean", line := 30, character := 2 }] }
  : ModuleSources)).compress
