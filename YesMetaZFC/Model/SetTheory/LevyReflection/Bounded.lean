import YesMetaZFC.Model.SetTheory.LevyReflection.Decode
import YesMetaZFC.SetTheory.Definitional.Project.Predicate
import YesMetaZFC.SetTheory.Definitional.Project.ClosedEnv
import YesMetaZFC.SetTheory.Definitional.Project.Hierarchy.Substitution

/-! # 原公式在集合载体上的有界化证书 -/
namespace YesMetaZFC.SetTheory
open Definitional.Project

theorem lr_rel_delta_l {n d} (φ : Formula 1 n) (X : Term d) (e : Fin n → Term d) :
    (lr_rel_m φ X e).IsDelta0 := by
  induction φ generalizing d with
  | falsum => exact .falsum
  | truth => exact .truth
  | mem _ _ => exact .mem _ _
  | atom _ _ _ => exact .atom _ _ _
  | neg _ ih => exact .neg (ih X e)
  | conj _ _ ih jh => exact .conj (ih X e) (jh X e)
  | disj _ _ ih jh => exact .disj (ih X e) (jh X e)
  | imp _ _ ih jh => exact .imp (ih X e) (jh X e)
  | iff _ _ ih jh => exact .iff (ih X e) (jh X e)
  | existsE _ ih => exact .existsMem _ (ih _ _)
  | forallE _ ih => exact .forallMem _ (ih _ _)

def lr_truth_s (φ : UnarySchema 1) : BinarySchema 1 where
  body := lr_rel_m φ.body (.bound 2) (Fin.cases .newest (fun _ => .bound 1))
  freeClosed := lr_rel_closed_l φ.body φ.freeClosed _ _ rfl (Fin.cases rfl (fun _ => rfl))

def Lr_truth_d {M : Structure} (φ : UnarySchema 1) (X q y : M.Domain) : Prop :=
  (lr_truth_s φ).denote (⟨fun _ => X, fun _ => X⟩ : Env M 1) q y

def lr_truth_m {d} (φ : UnarySchema 1) (X q y : Term d) : Formula 1 d :=
  binary_pred_m (lr_truth_s φ) (fun _ => X) q y

@[simp] theorem lr_truth_closed_l {d} (φ : UnarySchema 1) (X q y : Term d)
    (hX : X.freeSupport = []) (hq : q.freeSupport = []) (hy : y.freeSupport = []) :
    (lr_truth_m φ X q y).FreeClosed := binary_pred_closed_l _ _ _ _ (fun _ => hX) hq hy

private theorem pred_delta_l {n d} (φ : BinarySchema n) (hφ : φ.body.IsDelta0)
    (e : Fin n → Term d) (q y : Term d) : (binary_pred_m φ e q y).IsDelta0 := hφ.bind_l _

theorem lr_truth_delta_l {d} (φ : UnarySchema 1) (X q y : Term d) :
    (lr_truth_m φ X q y).IsDelta0 :=
  pred_delta_l (lr_truth_s φ) (lr_rel_delta_l ..) _ _ _

theorem lr_truth_sat_l {M : Structure} {d} (φ : UnarySchema 1) (ρ : Env M d) (X q y : Term d) :
    Formula.satisfies ρ (lr_truth_m φ X q y) ↔ Lr_truth_d φ (X.eval ρ) (q.eval ρ) (y.eval ρ) :=
  (binary_pred_sat_l (lr_truth_s φ) ρ (fun _ => X) q y).trans
    (Formula.closed_env_l _ (lr_truth_s φ).freeClosed
      (funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))

/-- 原公式反射到传递载体时，其有界真值就是背景原真值。 -/
theorem lr_truth_reflect_l {M : Structure} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) {c X R}
    (hM : Internal.Smdl_d I c X R)
    (hR : ∀ a b, M.PairMember I a b R ↔ M.mem a X ∧ M.mem b X ∧ M.mem a b)
    (ht : M.TransitiveSet X) (φ : UnarySchema 1) (hr : Lr_reflect_d φ.body X)
    {q y} (hq : M.mem q X) (hy : M.mem y X) :
    Lr_truth_d φ X q y ↔ φ.denote (⟨fun _ => q, fun _ => q⟩ : Env M 1) y := by
  let η : Env (Internal.smdl_structure_l I (R := R) hM.2.1) 1 :=
    ⟨fun _ => ⟨q, hq⟩, fun _ => ⟨q, hq⟩⟩
  exact (lr_rel_decode_l I hM hR ht φ.body φ.freeClosed (η.push ⟨y, hy⟩)
    (((⟨fun _ => X, fun _ => X⟩ : Env M 1).push q).push y) (.bound 2)
    (Fin.cases .newest (fun _ => .bound 1)) rfl (Fin.cases rfl (fun _ => rfl))).trans
    (lr_model_l I hM hR ht φ.body φ.freeClosed hr
      ((⟨fun _ => q, fun _ => q⟩ : Env M 1).push y) (η.push ⟨y, hy⟩)
      (Fin.cases rfl (fun _ => rfl))).symm

end YesMetaZFC.SetTheory
