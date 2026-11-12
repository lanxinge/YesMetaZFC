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

/-! ## 相对 Jensen 层的存在、唯一性与层级方程 -/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project
universe u
variable {M : Structure.{u}} (S : M.Domain)

def Ja_value_d (a Y : M.Domain) : Prop := (rc_value_s ja_op_s).schema.denote (ja_env_l S) a Y
def Ja_d (a Y : M.Domain) : Prop := M.IsOrdinal a ∧ Ja_value_d S a Y
def ja_value_m {d} (S a Y : Term d) : Formula 1 d :=
  binary_pred_m (rc_value_s ja_op_s).schema (fun _ => S) a Y
derive_free_closed ja_value_m

theorem ja_value_sat_l {d} (ρ : Env M d) (S a Y : Term d) :
    Formula.satisfies ρ (ja_value_m S a Y) ↔ Ja_value_d (S.eval ρ) (a.eval ρ) (Y.eval ρ) := by
  rw [ja_value_m, binary_pred_sat_l]
  exact Formula.closed_env_l _ (rc_value_s ja_op_s).schema.freeClosed rfl

theorem ja_value_exists_l (hM : M.Models KPi) (a : M.Domain) : ∃ Y, Ja_value_d S a Y := by
  obtain ⟨Y, hY⟩ := rc_value_exists_l hM ja_op_s (ja_env_l S) (ja_op_total_l hM _) (ja_op_unique_l hM _) a
  exact ⟨Y, (rc_value_sat_l (KPi.models_iff_l.mp hM).1.1 ..).mpr hY⟩

theorem ja_value_unique_l (hM : M.Models KPi) {a X Y : M.Domain}
    (hx : Ja_value_d S a X) (hy : Ja_value_d S a Y) : X = Y :=
  rc_value_unique_l hM ja_op_s (ja_env_l S) (ja_op_unique_l hM _)
    ((rc_value_sat_l (KPi.models_iff_l.mp hM).1.1 ..).mp hx)
    ((rc_value_sat_l (KPi.models_iff_l.mp hM).1.1 ..).mp hy)

theorem ja_equation_l (hM : M.Models KPi) {a Y} (h : Ja_value_d S a Y) (t : M.Domain) :
    M.mem t Y ↔ M.mem t S ∨ ∃ b, M.mem b a ∧ ∃ X, Ja_value_d S b X ∧
      ∃ Z, Jh_step_d X Z ∧ M.mem t Z := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨F, _, hf, he⟩ := rc_value_equation_l hM ja_op_s (ja_env_l S) (ja_op_unique_l hM _)
    ((rc_value_sat_l hKP.1 ..).mp h)
  obtain ⟨Z, hz, hY⟩ := (ja_op_sat_l hKP _ F Y).mp hf
  obtain ⟨R, P, hr, hp, hZ⟩ := (jh_op_sat_l hM _ F Z).mp hz
  apply (hY t).trans; apply or_congr_right
  rw [hZ t]
  constructor
  · rintro ⟨W, hw, ht⟩
    obtain ⟨X, hx, hs⟩ := (hp W).mp hw
    obtain ⟨b, hb⟩ := (hr X).mp hx
    exact ⟨b, ((he b X).mp hb).1, X, (rc_value_sat_l hKP.1 ..).mpr ((he b X).mp hb).2, W, hs, ht⟩
  · rintro ⟨b, hb, X, hx, W, hw, ht⟩
    exact ⟨W, (hp W).mpr ⟨X, (hr X).mpr ⟨b, (he b X).mpr
      ⟨hb, (rc_value_sat_l hKP.1 ..).mp hx⟩⟩, hw⟩, ht⟩

theorem ja_seed_l (hM : M.Models KPi) {a Y} (h : Ja_value_d S a Y) : M.MemberSubset S Y :=
  fun t ht => (ja_equation_l S hM h t).mpr (Or.inl ht)

theorem ja_mono_l (hM : M.Models KPi) {a b X Y} (hab : M.MemberSubset a b)
    (hx : Ja_value_d S a X) (hy : Ja_value_d S b Y) : M.MemberSubset X Y := by
  intro t ht
  apply (ja_equation_l S hM hy t).mpr
  rcases (ja_equation_l S hM hx t).mp ht with ht | ⟨c, hc, V, hv, Z, hz, ht⟩
  · exact Or.inl ht
  · exact Or.inr ⟨c, hab c hc, V, hv, Z, hz, ht⟩

theorem ja_mem_l (hM : M.Models KPi) {a b X Y} (hab : M.mem a b)
    (hx : Ja_value_d S a X) (hy : Ja_value_d S b Y) : M.mem X Y := by
  obtain ⟨Z, hz⟩ := jh_step_exists_l hM X
  exact (ja_equation_l S hM hy X).mpr (Or.inr ⟨a, hab, X, hx, Z, hz, (jh_step_spec_l hM hz).2.2⟩)

theorem ja_transitive_l (hM : M.Models KPi) (hS : M.TransitiveSet S) {a Y}
    (hy : Ja_value_d S a Y) : M.TransitiveSet Y := by
  let φ : UnarySchema 1 := { body := .forallE (.imp (ja_value_m (.bound 2) (.bound 1) .newest)
    (Formula.isTransitive .newest)) }
  have hφ b : φ.denote (ja_env_l S) b ↔ ∀ V, Ja_value_d S b V → M.TransitiveSet V := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      ja_value_sat_l, Formula.satisfies_isTransitive_iff]; rfl
  apply (hφ a).mp ((KPi.models_iff_l.mp hM).2 φ (ja_env_l S) ?_ a) Y hy
  intro b ih
  apply (hφ b).mpr
  intro V hv t ht z hz
  apply (ja_equation_l S hM hv z).mpr
  rcases (ja_equation_l S hM hv t).mp ht with ht | ⟨c, hc, X, hx, Z, hs, ht⟩
  · exact Or.inl (hS t ht z hz)
  · exact Or.inr ⟨c, hc, X, hx, Z, hs, jh_step_transitive_l hM ((hφ c).mp (ih c hc) X hx) hs t ht z hz⟩

theorem ja_zero_l (hM : M.Models KPi) {a Y} (ha : ∀ b, ¬ M.mem b a) (hy : Ja_value_d S a Y) : Y = S :=
  (KPi.models_iff_l.mp hM).1.1.eq_of_same_members Y S (fun t => (ja_equation_l S hM hy t).trans
    ⟨fun h => h.elim id (fun ⟨b, hb, _⟩ => (ha b hb).elim), Or.inl⟩)

theorem ja_successor_l (hM : M.Models KPi) {a s A B} (ha : M.IsOrdinal a)
    (hs : M.SuccessorOf s a) (hA : Ja_value_d S a A) (hB : Ja_value_d S s B) : Jh_step_d A B := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨C, hc⟩ := jh_step_exists_l hM A
  have he : B = C := by
    apply hKP.1.eq_of_same_members; intro t
    constructor
    · intro ht
      rcases (ja_equation_l S hM hB t).mp ht with ht | ⟨b, hb, X, hx, Z, hz, ht⟩
      · exact (jh_step_spec_l hM hc).2.1 t (ja_seed_l S hM hA t ht)
      · rcases (hs b).mp hb with hb | he
        · exact jh_step_le_l hM (ja_mono_l S hM (ha.transitive b hb) hx hA)
            (ja_mem_l S hM hb hx hA) hz hc t ht
        · have he := hKP.1.eq_of_same_members b a he; subst b
          have he := ja_value_unique_l S hM hx hA; subst X
          exact jh_step_unique_l hM hz hc ▸ ht
    · intro ht
      exact (ja_equation_l S hM hB t).mpr (Or.inr ⟨a, hs.predecessor_mem, A, hA, C, hc, ht⟩)
  exact he.symm ▸ hc

theorem ja_limit_l (hM : M.Models KPi) {a Y} (ha : M.IsLimitOrdinal a) (hy : Ja_value_d S a Y) (t : M.Domain) :
    M.mem t Y ↔ ∃ b, M.mem b a ∧ ∃ X, Ja_value_d S b X ∧ M.mem t X := by
  constructor
  · intro ht
    rcases (ja_equation_l S hM hy t).mp ht with ht | ⟨b, hb, X, hx, Z, hz, ht⟩
    · obtain ⟨b, hb⟩ := ha.2.1
      obtain ⟨X, hx⟩ := ja_value_exists_l S hM b
      exact ⟨b, hb, X, hx, ja_seed_l S hM hx t ht⟩
    · obtain ⟨c, hc, hbc⟩ := ha.2.2 b hb
      obtain ⟨V, hv⟩ := ja_value_exists_l S hM c
      exact ⟨c, hc, V, hv, (ja_equation_l S hM hv t).mpr (Or.inr ⟨b, hbc, X, hx, Z, hz, ht⟩)⟩
  · rintro ⟨b, hb, X, hx, ht⟩
    exact ja_mono_l S hM (ha.1.transitive b hb) hx hy t ht

end YesMetaZFC.SetTheory.InnerModel.Relative
