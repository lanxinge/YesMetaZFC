import YesMetaZFC.SetTheory.InnerModel.Jensen.Hierarchy

/-! # 以传递集合为基的 Jensen 递归

算子为 S∪⋃{Rud(X∪{X}) : X 是前值}。S 是实际内部参数；零层为 S，
后继和极限继续使用同一个内部 Σ₁ 递归，不把层级存在性作为输入。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project
universe u
variable {M : Structure.{u}}

def ja_core_s : S1_binary 1 where
  matrix := {
    body := jh_op_s.matrix_m Fin.elim0 (.bound 2) (.bound 1) .newest
    delta0 := jh_op_s.matrix.delta0.bind_l _ }

theorem ja_core_sat_l (ρ : Env M 1) (F Y : M.Domain) :
    ja_core_s.schema.denote ρ F Y ↔ jh_op_s.schema.denote ⟨Fin.elim0, ρ.free⟩ F Y := by
  simp only [S1_binary.sat_l, ja_core_s, S1_binary.matrix_sat_l]
  apply exists_congr; intro w
  apply Formula.closed_env_l _ jh_op_s.matrix.freeClosed
  exact funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))

def ja_join_s : S1_binary 1 := S1_binary.of_delta0 {
  body := .conj (Formula.forallMem .newest (.disj (.mem .newest (.bound 3)) (.mem .newest (.bound 2))))
    (.conj (Formula.forallMem (.bound 2) (.mem .newest (.bound 1)))
      (Formula.forallMem (.bound 1) (.mem .newest (.bound 1))))
  delta0 := .conj (.forallMem _ (.disj (.mem _ _) (.mem _ _)))
    (.conj (.forallMem _ (.mem _ _)) (.forallMem _ (.mem _ _))) }

theorem ja_join_sat_l (ρ : Env M 1) (X Y : M.Domain) :
    ja_join_s.schema.denote ρ X Y ↔ ∀ t, M.mem t Y ↔ M.mem t (ρ.bound 0) ∨ M.mem t X := by
  rw [ja_join_s, S1_binary.of_delta0_sat_l]
  simp only [BinarySchema.denote,
    Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_mem_iff]
  exact ⟨fun ⟨h, hs, hx⟩ t => ⟨h t, fun ht => ht.elim (hs t) (hx t)⟩,
    fun h => ⟨fun t => (h t).mp, (fun t ht => (h t).mpr (Or.inl ht)), fun t ht => (h t).mpr (Or.inr ht)⟩⟩

def ja_op_s : S1_binary 1 := ja_core_s.comp ja_join_s
def ja_env_l (S : M.Domain) : Env M 1 := ⟨fun _ => S, fun _ => S⟩

theorem ja_op_sat_l (hKP : M.Models KP) (ρ : Env M 1) (F Y : M.Domain) :
    ja_op_s.schema.denote ρ F Y ↔ ∃ Z, jh_op_s.schema.denote ⟨Fin.elim0, ρ.free⟩ F Z ∧
      ∀ t, M.mem t Y ↔ M.mem t (ρ.bound 0) ∨ M.mem t Z := by
  simp only [ja_op_s, S1_binary.comp_sat_l hKP, ja_core_sat_l, ja_join_sat_l]

theorem ja_op_total_l (hM : M.Models KPi) (ρ : Env M 1) (F : M.Domain) :
    ∃ Y, ja_op_s.schema.denote ρ F Y := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨Z, hz⟩ := jh_op_total_l hM ⟨Fin.elim0, ρ.free⟩ F
  obtain ⟨P, hp⟩ := KP.exists_pair hKP (ρ.bound 0) Z
  obtain ⟨Y, hy⟩ := KP.exists_union hKP P
  refine ⟨Y, (ja_op_sat_l hKP ρ F Y).mpr ⟨Z, hz, fun t => (hy t).trans ?_⟩⟩
  exact ⟨fun ⟨a, ha, ht⟩ => ((hp a).mp ha).elim (fun h => Or.inl (h ▸ ht)) (fun h => Or.inr (h ▸ ht)),
    fun h => h.elim (fun h => ⟨_, (hp _).mpr (Or.inl rfl), h⟩) (fun h => ⟨_, (hp _).mpr (Or.inr rfl), h⟩)⟩

theorem ja_op_unique_l (hM : M.Models KPi) (ρ : Env M 1) (F Y Z : M.Domain)
    (hy : ja_op_s.schema.denote ρ F Y) (hz : ja_op_s.schema.denote ρ F Z) : Y = Z := by
  obtain ⟨U, hu, hY⟩ := (ja_op_sat_l (KPi.models_iff_l.mp hM).1 ρ F Y).mp hy
  obtain ⟨V, hv, hZ⟩ := (ja_op_sat_l (KPi.models_iff_l.mp hM).1 ρ F Z).mp hz
  have h := jh_op_unique_l hM _ F U V hu hv; subst V
  exact (KPi.models_iff_l.mp hM).1.1.eq_of_same_members Y Z (fun t => (hY t).trans (hZ t).symm)

end YesMetaZFC.SetTheory.InnerModel.Relative
