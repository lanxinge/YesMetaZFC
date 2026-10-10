import YesMetaZFC.SetTheory.Descriptive.RealPair

/-! # 内部实数投影与相对补

投影量化的是模型内 Baire 空间的成员；关系自身也是模型中的集合。
投影、补以及先补后投影都有原公式、实际集合输出和唯一性。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Cm_d (B K L : M.Domain) : Prop := ∀ x, M.mem x L ↔ M.mem x B ∧ ¬ M.mem x K
def cm_m {d} (B K L : Term d) : Formula 1 d := Formula.isDifference L B K
derive_free_closed cm_m
theorem cm_sat_l {d} (ρ : Env M d) (B K L : Term d) :
    Formula.satisfies ρ (cm_m B K L) ↔ Cm_d (M := M) (B.eval ρ) (K.eval ρ) (L.eval ρ) := by
  simp only [cm_m, Formula.isDifference, Cm_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_neg_iff, Definitional.Term.eval_weaken]; rfl

omit I in
theorem cm_exists_l (hKP : M.Models KP) (B K : M.Domain) : ∃ L, Cm_d B K L := KP.difference_exists_d hKP K B
omit I in
theorem cm_unique_l (hE : Extensional M) {B K L V : M.Domain} (h : Cm_d B K L) (k : Cm_d B K V) : L = V :=
  hE.eq_of_same_members L V (fun x => (h x).trans (k x).symm)
omit I in
theorem cm_symm_l {B K L : M.Domain} (hK : M.MemberSubset K B) (h : Cm_d B K L) : Cm_d B L K := by
  classical
  intro x
  exact ⟨fun hx => ⟨hK x hx, fun hl => ((h x).mp hl).2 hx⟩,
    fun ⟨hx, hn⟩ => Classical.byContradiction (fun hk => hn ((h x).mpr ⟨hx, hk⟩))⟩

def Prv_d (B J R x : M.Domain) : Prop := ∃ y z,
  M.mem y B ∧ M.mem z B ∧ Rp_d I J x y z ∧ M.mem z R
def prv_m {d} (B J R x : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (.mem (.bound 1) B.weaken.weaken) (.conj (.mem .newest B.weaken.weaken)
    (.conj (rp_m (𝒞 := 𝒞) J.weaken.weaken x.weaken.weaken (.bound 1) .newest) (.mem .newest R.weaken.weaken)))))
derive_free_closed prv_m
theorem prv_sat_l {d} (ρ : Env M d) (B J R x : Term d) :
    Formula.satisfies ρ (prv_m (𝒞 := 𝒞) B J R x) ↔ Prv_d I (B.eval ρ) (J.eval ρ) (R.eval ρ) (x.eval ρ) := by
  simp only [prv_m, Prv_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, rp_sat_l I, Definitional.Term.eval_weaken]; rfl

def Pr_d (B J R K : M.Domain) : Prop := ∀ x, M.mem x K ↔ M.mem x B ∧ Prv_d I B J R x
def pr_m {d} (B J R K : Term d) : Formula 1 d := .forallE (.iff (.mem .newest K.weaken)
  (.conj (.mem .newest B.weaken) (prv_m (𝒞 := 𝒞) B.weaken J.weaken R.weaken .newest)))
derive_free_closed pr_m

theorem pr_sat_l {d} (ρ : Env M d) (B J R K : Term d) :
    Formula.satisfies ρ (pr_m (𝒞 := 𝒞) B J R K) ↔ Pr_d I (B.eval ρ) (J.eval ρ) (R.eval ρ) (K.eval ρ) := by
  simp only [pr_m, Pr_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, prv_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem pr_exists_l (hZF : M.Models ZF) (B J R : M.Domain) : ∃ K, Pr_d I B J R K := by
  let ρ : Env M 3 := ((⟨fun _ => B, fun _ => B⟩ : Env M 1).push J).push R
  let φ : UnarySchema 3 := { body := prv_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨K, hK⟩ := ZF.separation_exists_d hZF φ ρ B
  exact ⟨K, fun x => (hK x).trans (and_congr_right fun _ => prv_sat_l I _ _ _ _ _)⟩

theorem pr_unique_l (hE : Extensional M) {B J R K L} (h : Pr_d I B J R K) (k : Pr_d I B J R L) : K = L :=
  hE.eq_of_same_members K L (fun x => (h x).trans (k x).symm)

theorem pr_mono_l {B J R Q K L} (h : Pr_d I B J R K) (k : Pr_d I B J Q L)
    (hRQ : M.MemberSubset R Q) : M.MemberSubset K L := by
  intro x hx
  obtain ⟨hxB, y, z, hy, hz, hp, hr⟩ := (h x).mp hx
  exact (k x).mpr ⟨hxB, y, z, hy, hz, hp, hRQ z hr⟩

def Pstep_d (B J K L : M.Domain) : Prop := ∃ C, Cm_d B K C ∧ Pr_d I B J C L
def pstep_m {d} (B J K L : Term d) : Formula 1 d := .existsE (.conj (cm_m B.weaken K.weaken .newest)
  (pr_m (𝒞 := 𝒞) B.weaken J.weaken .newest L.weaken))
derive_free_closed pstep_m
theorem pstep_sat_l {d} (ρ : Env M d) (B J K L : Term d) :
    Formula.satisfies ρ (pstep_m (𝒞 := 𝒞) B J K L) ↔ Pstep_d I (B.eval ρ) (J.eval ρ) (K.eval ρ) (L.eval ρ) := by
  simp only [pstep_m, Pstep_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    cm_sat_l, pr_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem pstep_exists_l (hZF : M.Models ZF) (B J K : M.Domain) : ∃ L, Pstep_d I B J K L := by
  obtain ⟨C, hC⟩ := cm_exists_l (ZF.modelsKP hZF) B K
  obtain ⟨L, hL⟩ := pr_exists_l I hZF B J C
  exact ⟨L, C, hC, hL⟩

theorem pstep_unique_l (hE : Extensional M) {B J K L V} (h : Pstep_d I B J K L) (k : Pstep_d I B J K V) : L = V := by
  obtain ⟨C, hC, hL⟩ := h
  obtain ⟨D, hD, hV⟩ := k
  exact pr_unique_l I hE hL (cm_unique_l hE hD hC ▸ hV)

end YesMetaZFC.SetTheory.Descriptive
