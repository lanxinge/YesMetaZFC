import YesMetaZFC.SetTheory.InnerModel.Recursion.Existence
import YesMetaZFC.SetTheory.Definitional.Project.ClosedEnv

/-! # 模型内部的隶属坍塌递归

固定集合 X，递归定义 π(a)={π(b) : b∈a∩X}。算子只从前段图读取 X 中的
索引；全部递归证书由已有 KPi 成员递归构造，不假定模型外部良基。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Mc_op_d (X F Y : M.Domain) : Prop := ∀ y, M.mem y Y ↔ ∃ x, M.mem x X ∧ Rd_entry_d x y F

def mc_op_m {n} (X F Y : Term n) : Formula 1 n :=
  .conj (Formula.forallMem Y (Formula.existsMem X.weaken (rd_entry0_m .newest (.bound 1) F.weaken.weaken)))
    (Formula.forallMem X (Formula.forallMem F.weaken (Formula.forallMem .newest (Formula.forallMem .newest
      (.imp (kpair0_m (.bound 2) (.bound 3) .newest) (.mem .newest Y.weaken.weaken.weaken.weaken))))))
derive_free_closed mc_op_m
theorem mc_op_delta_l {n} (X F Y : Term n) : (mc_op_m X F Y).IsDelta0 :=
  .conj (.forallMem _ (.existsMem _ (rd_entry0_delta_l ..)))
    (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.imp (kpair0_delta_l ..) (.mem _ _))))))

theorem mc_op_formula_l (hE : Extensional M) {n} (ρ : Env M n) (X F Y : Term n) :
    Formula.satisfies ρ (mc_op_m X F Y) ↔ Mc_op_d (X.eval ρ) (F.eval ρ) (Y.eval ρ) := by
  simp only [mc_op_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, rd_entry0_sat_l hE, Formula.satisfies_imp_iff,
    kpair0_sat_l hE, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨h, g⟩ y
    refine ⟨h y, fun ⟨x, hx, p, hp, hpF⟩ => ?_⟩
    obtain ⟨q, hq, hy⟩ := (kpair_union_l M hp y).mpr (Or.inr rfl)
    exact g x hx p hpF q hq y hy hp
  · intro h
    exact ⟨fun y => (h y).mp, fun x hx p hp _ _ y _ hpair => (h y).mpr ⟨x, hx, p, hpair, hp⟩⟩

def mc_op_s : S1_binary 1 := .of_delta0 {
  body := mc_op_m (.bound 2) (.bound 1) .newest, delta0 := mc_op_delta_l .. }
theorem mc_op_sat_l (hE : Extensional M) (ρ : Env M 1) (F Y : M.Domain) :
    mc_op_s.schema.denote ρ F Y ↔ Mc_op_d (ρ.bound 0) F Y :=
  (S1_binary.of_delta0_sat_l _ ρ F Y).trans (mc_op_formula_l hE ((ρ.push F).push Y) (.bound 2) (.bound 1) .newest)

theorem mc_op_exists_l (hKP : M.Models KP) (X F : M.Domain) : ∃ Y, Mc_op_d X F Y := by
  obtain ⟨R, hr⟩ := rd_fun_exists_l hKP .range F F F
  let φ : Delta0UnarySchema 2 := {
    body := Formula.existsMem (.bound 1) (rd_entry0_m .newest (.bound 1) (.bound 3))
    delta0 := .existsMem _ (rd_entry0_delta_l ..) }
  let ρ : Env M 2 := ⟨Fin.cases X (fun _ => F), fun _ => X⟩
  have sat y : φ.toUnarySchema.denote ρ y ↔ ∃ x, M.mem x X ∧ Rd_entry_d x y F := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hKP.1]; rfl
  obtain ⟨Y, hy⟩ := KP.separation_exists_d hKP φ ρ R
  exact ⟨Y, fun y => (hy y).trans ((and_congr_right fun _ => sat y).trans
    ⟨And.right, fun ⟨x, hx, he⟩ => ⟨(hr y).mpr ⟨x, he⟩, x, hx, he⟩⟩)⟩

theorem mc_op_unique_l (hE : Extensional M) {X F Y Z : M.Domain} (h : Mc_op_d X F Y) (g : Mc_op_d X F Z) : Y = Z :=
  hE.eq_of_same_members Y Z (fun y => (h y).trans (g y).symm)

def mc_env_l (X : M.Domain) : Env M 1 := ⟨fun _ => X, fun _ => X⟩
def Mc_value_d (X x y : M.Domain) : Prop := Rc_value_d mc_op_s (mc_env_l X) x y
def mc_value_m {n} (X x y : Term n) : Formula 1 n := binary_pred_m (rc_value_s mc_op_s).schema (fun _ => X) x y
derive_free_closed mc_value_m
theorem mc_value_sat_l (hE : Extensional M) {n} (ρ : Env M n) (X x y : Term n) :
    Formula.satisfies ρ (mc_value_m X x y) ↔ Mc_value_d (X.eval ρ) (x.eval ρ) (y.eval ρ) := by
  rw [mc_value_m, binary_pred_sat_l]
  apply Iff.trans ?_ (rc_value_sat_l hE mc_op_s (mc_env_l (X.eval ρ)) (x.eval ρ) (y.eval ρ))
  exact Formula.closed_env_l _ (rc_value_s mc_op_s).schema.freeClosed rfl

theorem mc_value_exists_l (hM : M.Models KPi) (X x : M.Domain) : ∃ y, Mc_value_d X x y := by
  let hKP := (KPi.models_iff_l.mp hM).1
  exact rc_value_exists_l hM mc_op_s (mc_env_l X)
    (fun F => (mc_op_exists_l hKP X F).imp fun y hy => (mc_op_sat_l hKP.1 _ F y).mpr hy)
    (fun _ _ _ h g => mc_op_unique_l hKP.1 ((mc_op_sat_l hKP.1 ..).mp h) ((mc_op_sat_l hKP.1 ..).mp g)) x

theorem mc_value_unique_l (hM : M.Models KPi) {X x y z : M.Domain} (h : Mc_value_d X x y) (g : Mc_value_d X x z) : y = z :=
  rc_value_unique_l hM mc_op_s (mc_env_l X) (fun _ _ _ h g => mc_op_unique_l (KPi.models_iff_l.mp hM).1.1
    ((mc_op_sat_l (KPi.models_iff_l.mp hM).1.1 ..).mp h) ((mc_op_sat_l (KPi.models_iff_l.mp hM).1.1 ..).mp g)) h g

theorem mc_value_equation_l (hM : M.Models KPi) {X a Y : M.Domain} (h : Mc_value_d X a Y) (y : M.Domain) :
    M.mem y Y ↔ ∃ x, M.mem x a ∧ M.mem x X ∧ Mc_value_d X x y := by
  let hE := (KPi.models_iff_l.mp hM).1.1
  obtain ⟨F, _, hf, he⟩ := rc_value_equation_l hM mc_op_s (mc_env_l X)
    (fun _ _ _ h g => mc_op_unique_l hE ((mc_op_sat_l hE ..).mp h) ((mc_op_sat_l hE ..).mp g)) h
  rw [(mc_op_sat_l hE _ F Y).mp hf y]
  exact ⟨fun ⟨x, hx, hp⟩ => ⟨x, ((he x y).mp hp).1, hx, ((he x y).mp hp).2⟩,
    fun ⟨x, hxa, hx, hy⟩ => ⟨x, hx, (he x y).mpr ⟨hxa, hy⟩⟩⟩

end YesMetaZFC.SetTheory
