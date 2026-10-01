import YesMetaZFC.SetTheory.InnerModel.ProofCode.Parser.Names

/-! # 初段计算的统一候选集合与有界切片 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Pi_box_d (a ω C B : M.Domain) : Prop := ∃ S P, M.SuccessorOf S a ∧
  Rd_fun_d .prod ω C ω P ∧ Rd_fun_d .prod S P S B

theorem pi_box_exists_l (hKP : M.Models KP) (a ω C : M.Domain) : ∃ B, Pi_box_d a ω C B := by
  obtain ⟨S, hs⟩ := KP.exists_successor hKP a
  obtain ⟨P, hp⟩ := rd_fun_exists_l hKP .prod ω C ω
  obtain ⟨B, hb⟩ := rd_fun_exists_l hKP .prod S P S
  exact ⟨B, S, P, hs, hp, hb⟩

theorem pi_box_mem_l (hE : Extensional M) {a ω C B : M.Domain} (hb : Pi_box_d a ω C B) (v : M.Domain) :
    M.mem v B ↔ ∃ b, (M.mem b a ∨ b = a) ∧ ∃ n, M.mem n ω ∧ ∃ c, M.mem c C ∧ Rd_triple_d v b n c := by
  obtain ⟨S, P, hs, hp, hb⟩ := hb
  constructor
  · intro hv
    obtain ⟨b, p, hbS, hpP, hv⟩ := (hb v).mp hv
    obtain ⟨n, c, hn, hc, hp⟩ := (hp p).mp hpP
    exact ⟨b, ((hs b).mp hbS).imp_right (hE.eq_of_same_members _ _), n, hn, c, hc, p, hp, hv⟩
  · rintro ⟨b, hbS, n, hn, c, hc, p, hp', hv⟩
    exact (hb v).mpr ⟨b, p, (hs b).mpr (hbS.imp_right (fun (he : b = a) => he ▸ (fun _ => Iff.rfl))),
      (hp p).mpr ⟨n, c, hn, hc, hp'⟩, hv⟩

theorem pi_box_family_l (hE : Extensional M) {a ω C B : M.Domain}
    (ha : M.IsOrdinal a) (hω : Omega0_d ω) (hb : Pi_box_d a ω C B) :
    ∀ v, M.mem v B → ∃ b n c, Rd_triple_d v b n c ∧ M.IsOrdinal b ∧ KP.N0_d n ∧ M.mem c C := by
  intro v hv
  obtain ⟨b, hb, n, hn, c, hc, hv⟩ := (pi_box_mem_l hE hb v).mp hv
  exact ⟨b, n, c, hv, hb.elim ha.mem (fun he => he.symm ▸ ha), hω.2 n hn, hc⟩

theorem pi_box_contains_l (hM : M.Models KPi) {w a h c ω C B : M.Domain}
    (hw : Pn_name_d w a h c) (hω : Omega0_d ω) (hc : Rd_closure_d a C) (hb : Pi_box_d a ω C B) : M.mem w B := by
  obtain ⟨R, hr, hcR⟩ := hw.2.2.2.2
  have he := rd_closure_unique_l hM hr hc; subst R
  exact (pi_box_mem_l (KPi.models_iff_l.mp hM).1.1 hb w).mpr
    ⟨a, Or.inr rfl, h, KPi.n0_in_inductive_l hM hω.1 hw.2.2.1, c, hcR, hw.1⟩

theorem pi_box_predecessor_l (hM : M.Models KPi) {w a h c ω C B v : M.Domain}
    (hw : Pn_name_d w a h c) (hω : Omega0_d ω) (hc : Rd_closure_d a C) (hb : Pi_box_d a ω C B)
    (hv : Pn_valid_d v) (hlt : Pn_lt_d v w) : M.mem v B := by
  obtain ⟨b, n, d, hp, _, hn, _, R, hr, hd⟩ := hv
  have hba : M.mem b a ∨ b = a := ((pn_lt_iff_l hp hw.1).mp hlt).elim Or.inl (fun h => Or.inr h.1)
  have sub : M.MemberSubset b a := fun x hx => hba.elim (fun hb => hw.2.1.transitive b hb x hx) (fun he => he ▸ hx)
  exact (pi_box_mem_l (KPi.models_iff_l.mp hM).1.1 hb v).mpr
    ⟨b, hba, n, KPi.n0_in_inductive_l hM hω.1 hn, d, rd_closure_mono_l hM sub hr hc d hd, hp⟩

def pi_test_s (φ : S1_binary 0) : Delta0BinarySchema 1 where
  body := φ.matrix_m Fin.elim0 (.bound 1) (.bound 2) .newest
  freeClosed := by simp -implicitDefEqProofs
  delta0 := φ.matrix.delta0.bind_l _
theorem pi_test_sat_l (φ : S1_binary 0) (ρ : Env M 1) (v : M.Domain) :
    (∃ W, (pi_test_s φ).toBinarySchema.denote ρ v W) ↔ φ.schema.denote (jh_env_l v) v (ρ.bound 0) := by
  simp only [BinarySchema.denote, pi_test_s, po_matrix_env_l φ (jh_env_l v)]
  exact (φ.sat_l (jh_env_l v) v (ρ.bound 0)).symm

def pi_slice_s : S1_binary 1 := S1_binary.separate (pi_test_s pn_lt_s) (pi_test_s pn_not_lt_s)
theorem pi_slice_sat_l (hM : M.Models KPi) {w X I : M.Domain} (hw : Pn_valid_d w) (hx : ∀ v, M.mem v X → Pn_valid_d v) :
    pi_slice_s.schema.denote (rd_seed_env_l w) X I ↔ ∀ v, M.mem v I ↔ M.mem v X ∧ Pn_lt_d v w := by
  rw [pi_slice_s, S1_binary.separate_sat_l (KPi.models_iff_l.mp hM).1 _ _ _ _ _ (fun v hv => by
    rw [pi_test_sat_l, pi_test_sat_l]; exact pn_delta1_l hM (hx v hv) hw (jh_env_l v))]
  simp only [pi_test_sat_l, pn_lt_sat_l (KPi.models_iff_l.mp hM).1]; rfl
theorem pi_slice_exists_l (hM : M.Models KPi) {w X : M.Domain} (hw : Pn_valid_d w) (hx : ∀ v, M.mem v X → Pn_valid_d v) :
    ∃ I, pi_slice_s.schema.denote (rd_seed_env_l w) X I := by
  obtain ⟨I, hi⟩ := pn_initial_in_l hM hx hw
  exact ⟨I, (pi_slice_sat_l hM hw hx).mpr hi⟩

def Pi_wit_d (φ : S1_binary 1) (a x y W : M.Domain) : Prop := φ.matrix_binary.toBinarySchema.denote ((rd_seed_env_l a).push x) y W
def pi_wit_m {n} (φ : S1_binary 1) (a x y W : Term n) : Formula 1 n := φ.matrix_m (fun _ => a) x y W
derive_free_closed pi_wit_m
theorem pi_wit_sat_l (φ : S1_binary 1) {n} (ρ : Env M n) (a x y W : Term n) :
    Formula.satisfies ρ (pi_wit_m φ a x y W) ↔ Pi_wit_d φ (a.eval ρ) (x.eval ρ) (y.eval ρ) (W.eval ρ) := by
  rw [pi_wit_m, S1_binary.matrix_sat_l]
  exact Formula.closed_env_l _ φ.matrix.freeClosed rfl
theorem pi_wit_value_l (φ : S1_binary 1) (a x y : M.Domain) : (∃ W, Pi_wit_d φ a x y W) ↔ φ.schema.denote (rd_seed_env_l a) x y :=
  (φ.sat_l (rd_seed_env_l a) x y).symm

end YesMetaZFC.SetTheory.InnerModel
