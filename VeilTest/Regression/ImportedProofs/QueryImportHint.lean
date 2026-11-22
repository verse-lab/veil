module

public import VeilTest.Regression.ImportedProofs.Spec

veil module NodeProofs

/-- error: To interpret this model, add `meta import VeilTest.Regression.ImportedProofs.Spec` alongside its regular import in the checking file. -/
#guard_msgs (substring := true) in
#model_check interpreted { node := Fin 2 } {}

/-- error: Could not display the trace. Add `meta import VeilTest.Regression.ImportedProofs.Spec` alongside its regular import in the checking file to evaluate the model's display instances. -/
#guard_msgs (error, drop info) in
sat trace {}

end NodeProofs
