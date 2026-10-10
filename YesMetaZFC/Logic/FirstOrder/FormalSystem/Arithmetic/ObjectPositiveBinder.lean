import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicSyntaxTransport
import YesMetaZFC.Logic.FirstOrder.FreshVariable
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.FiniteOrdinal

/-! # 正反射见证块的公共槽位运输 -/
namespace YesMetaZFC.Automation.ObjectPositiveBinder
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT
set_option autoImplicit false

/-- 替换穿过一个 binder，再打开为新 free 槽；所有尾槽只做 weakening。 -/
theorem open_substitute {bound free target : SetContext} (body : SetFormula (SetSort.set :: bound) free)
    (bs : VariableSubstitution signature bound [] target) (fs : VariableSubstitution signature free [] target) :
    (body.substituteMapped (VariableSubstitution.liftBound SetSort.set bs) (VariableSubstitution.weakenBound SetSort.set fs)).openBoundTop SetSort.set =
      body.substituteMapped (VariableSubstitution.cons (.fvar .here) (fun entry => (bs entry).weakenFree SetSort.set))
        (fun entry => (fs entry).weakenFree SetSort.set) := by
  unfold Formula.openBoundTop
  rw [Formula.substituteMapped_comp]
  congr 1
  · funext sort entry
    cases entry with
    | here => rfl
    | there entry => exact Term.openBoundTop_weakenBound SetSort.set (bs entry)
  · funext sort entry
    exact Term.openBoundTop_weakenBound SetSort.set (fs entry)

end YesMetaZFC.Automation.ObjectPositiveBinder
