import YesMetaZFC.SetTheory.InnerModel.Jensen.Hierarchy
import YesMetaZFC.SetTheory.KP.Ordinal

/-! # 全部内部 J 层的并类及其实际 Σ₁ 定义 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def L_d (x : M.Domain) : Prop := ∃ a Y, J_d a Y ∧ M.mem x Y

def l0_m {n} (T x : Term n) : Formula 1 n :=
  Formula.existsMem T (Formula.existsMem T.weaken
    (.conj (KP.ord0_m (.bound 1)) (.conj (.mem x.weaken.weaken .newest)
      ((rc_value_s jh_op_s).matrix_m Fin.elim0 (.bound 1) .newest T.weaken.weaken))))
derive_free_closed l0_m

theorem l0_delta_l {n} (T x : Term n) : (l0_m T x).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (KP.ord0_delta_l _)
    (.conj (.mem _ _) ((rc_value_s jh_op_s).matrix.delta0.bind_l _))))

def L0_d (T x : M.Domain) : Prop := ∃ a Y, M.mem a T ∧ M.mem Y T ∧ M.IsOrdinal a ∧ M.mem x Y ∧
  ∃ A F, Rc_cert_d jh_op_s (jh_env_l a) A F T ∧ M.mem a A ∧ Rd_entry_d a Y F

theorem l0_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (T x : Term n) :
    Formula.satisfies ρ (l0_m T x) ↔ L0_d (T.eval ρ) (x.eval ρ) := by
  have hc (η : Env M 0) a Y W : (rc_value_s jh_op_s).matrix_binary.toBinarySchema.denote
      (η.push a) Y W ↔
      ∃ A F, Rc_cert_d jh_op_s (jh_env_l a) A F W ∧ M.mem a A ∧ Rd_entry_d a Y F := by
    apply Iff.trans ?_ (rc_matrix_sat_l hKP.1 jh_op_s (jh_env_l a) a Y W)
    exact Formula.closed_env_l _ (rc_value_s jh_op_s).matrix.freeClosed
      (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))
  simp only [l0_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    KP.ord0_sat_l hKP, Formula.satisfies_mem_iff, S1_binary.matrix_sat_l, hc,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Term.eval_bound_one_push, Term.eval_bound_zero_push]
  change (∃ a, M.mem a (T.eval ρ) ∧ ∃ Y, M.mem Y (T.eval ρ) ∧ M.IsOrdinal a ∧ M.mem (x.eval ρ) Y ∧
    ∃ A F, Rc_cert_d jh_op_s (jh_env_l a) A F (T.eval ρ) ∧ M.mem a A ∧ Rd_entry_d a Y F) ↔ _
  exact ⟨fun ⟨a, ha, Y, hY, ho, hx, h⟩ => ⟨a, Y, ha, hY, ho, hx, h⟩,
    fun ⟨a, Y, ha, hY, ho, hx, h⟩ => ⟨a, ha, Y, hY, ho, hx, h⟩⟩

theorem l_witness_l (hE : Extensional M) (x : M.Domain) : L_d x ↔ ∃ T, L0_d T x := by
  constructor
  · rintro ⟨a, Y, ha, hx⟩
    obtain ⟨T, A, F, hf, hA, hF⟩ := (rc_value_sat_l hE jh_op_s (jh_env_l a) a Y).mp ha.2
    exact ⟨T, a, Y, hf.trans A hf.domain a hA, (hf.function.bound_l hF).2, ha.1, hx, A, F, hf, hA, hF⟩
  · rintro ⟨T, a, Y, _, _, ho, hx, A, F, hf, hA, hF⟩
    exact ⟨a, Y, ⟨ho, (rc_value_sat_l hE ..).mpr ⟨T, A, F, hf, hA, hF⟩⟩, hx⟩

def l_s : S1_binary 0 where
  matrix := { body := l0_m .newest (.bound 2), delta0 := l0_delta_l .. }
def l_m {n} (x : Term n) : Formula 1 n := .existsE (l0_m .newest x.weaken)
derive_free_closed l_m

theorem l_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (x : Term n) :
    Formula.satisfies ρ (l_m x) ↔ L_d (x.eval ρ) := by
  simp only [l_m, Formula.satisfies_exists_iff, l0_sat_l hKP,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
  exact (l_witness_l hKP.1 _).symm

theorem l_s_sat_l (hKP : M.Models KP) (ρ : Env M 0) (x y : M.Domain) :
    l_s.schema.denote ρ x y ↔ L_d x := by
  rw [S1_binary.sat_l]
  change (∃ T, Formula.satisfies (((ρ.push x).push y).push T) (l0_m .newest (.bound 2))) ↔ _
  simpa only [l0_sat_l hKP, Definitional.Term.eval_newest, Term.eval_bound_two_push,
    Term.eval_bound_one_push, Term.eval_bound_zero_push] using (l_witness_l hKP.1 x).symm

theorem l_transitive_l (hM : M.Models KPi) {x y : M.Domain} (hx : L_d x) (hy : M.mem y x) : L_d y := by
  obtain ⟨a, Y, ha, hx⟩ := hx
  exact ⟨a, Y, ha, jh_value_transitive_l hM ha.2 x hx y hy⟩

theorem l_layer_l (hM : M.Models KPi) {a Y : M.Domain} (ha : J_d a Y) : L_d Y := by
  obtain ⟨s, ho, hs⟩ := KP.ordinal_successor_l (KPi.models_iff_l.mp hM).1 ha.1
  obtain ⟨Z, hz⟩ := jh_value_exists_l hM s
  exact ⟨s, Z, ⟨ho, hz⟩, jh_value_mem_l hM hs.predecessor_mem ha.2 hz⟩

theorem l_bound_witness_l (hM : M.Models KPi) (B : M.Domain) :
    ∃ a Y, J_d a Y ∧ ∀ T, M.mem T B → ∀ x, L0_d T x → M.mem x Y := by
  obtain ⟨a, ha, hB⟩ := KPi.ordinal_bound_l hM B
  obtain ⟨Y, hy⟩ := jh_value_exists_l hM a
  refine ⟨a, Y, ⟨ha, hy⟩, fun T hT x hx => ?_⟩
  obtain ⟨b, X, hb, _, ho, hx, A, F, hf, hA, hF⟩ := hx
  have hX : Jh_value_d b X := (rc_value_sat_l (KPi.models_iff_l.mp hM).1.1 ..).mpr ⟨T, A, F, hf, hA, hF⟩
  exact jh_value_transitive_l hM hy X (jh_value_mem_l hM (hB T hT b hb ho) hX hy) x hx

theorem l_bound_l (hM : M.Models KPi) {X : M.Domain} (hx : ∀ x, M.mem x X → L_d x) :
    ∃ a Y, J_d a Y ∧ M.MemberSubset X Y := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨B, hB⟩ := KP.s1_collection_l hKP l_s (jh_env_l X) X
    (fun x h => ⟨x, (l_s_sat_l hKP _ x x).mpr (hx x h)⟩)
  obtain ⟨a, Y, ha, hb⟩ := l_bound_witness_l hM B
  refine ⟨a, Y, ha, fun x hx => ?_⟩
  obtain ⟨_, _, T, hT, hw⟩ := hB x hx
  exact hb T hT x ((l0_sat_l hKP _ _ _).mp hw)

end YesMetaZFC.SetTheory.InnerModel
