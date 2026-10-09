import YesMetaZFC.SetTheory.FlatPairing.Tag

/-! # 原平坦有序对约定的实际解释

有序对是左集合成员的左标签像与右集合成员的右标签像之并。
两类标签的不交性及单射性恢复两个坐标；由此直接实现原约定的解释实例。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Fp_pair_d (ω x y p : M.Domain) : Prop := ∀ z,
  M.mem z p ↔ (∃ a, M.mem a x ∧ Fp_tag_d false ω a z) ∨ ∃ b, M.mem b y ∧ Fp_tag_d true ω b z

def fp_pair0_m {d} (ω x y p : Term d) : Formula 1 d := .conj
  (Formula.forallMem p (.disj
    (Formula.existsMem x.weaken (fp_tag0_m false ω.weaken.weaken .newest (.bound 1)))
    (Formula.existsMem y.weaken (fp_tag0_m true ω.weaken.weaken .newest (.bound 1)))))
  (.conj (Formula.forallMem x (Formula.existsMem p.weaken (fp_tag0_m false ω.weaken.weaken (.bound 1) .newest)))
    (Formula.forallMem y (Formula.existsMem p.weaken (fp_tag0_m true ω.weaken.weaken (.bound 1) .newest))))
derive_free_closed fp_pair0_m

theorem fp_pair0_delta_l {d} (ω x y p : Term d) : (fp_pair0_m ω x y p).IsDelta0 :=
  .conj (.forallMem _ (.disj (.existsMem _ (fp_tag0_delta_l ..)) (.existsMem _ (fp_tag0_delta_l ..))))
    (.conj (.forallMem _ (.existsMem _ (fp_tag0_delta_l ..))) (.forallMem _ (.existsMem _ (fp_tag0_delta_l ..))))

theorem fp_pair_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω x y p : Term d) :
    Formula.satisfies ρ (FlatPairing.codeOver p x y ω) ↔ Fp_pair_d (ω.eval ρ) (x.eval ρ) (y.eval ρ) (p.eval ρ) := by
  have left {k} (η : Env M k) (W a z : Term k) := fp_tag_sat_l hE η false W a z
  have right {k} (η : Env M k) (W a z : Term k) := fp_tag_sat_l hE η true W a z
  simp only [Bool.false_eq_true, ↓reduceIte] at left right
  simp only [FlatPairing.codeOver, Fp_pair_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_disj_iff, Formula.satisfies_existsMem_iff, left, right,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem Fp_pair_d.unique_l (hE : Extensional M) {ω x y p q : M.Domain}
    (h : Fp_pair_d ω x y p) (k : Fp_pair_d ω x y q) : p = q :=
  hE.eq_of_same_members p q (fun z => (h z).trans (k z).symm)

theorem fp_pair_exists_l (hKP : M.Models KP) {ω : M.Domain} (hω : M.IsInductive ω) (x y : M.Domain) :
    ∃ p, Fp_pair_d ω x y p := by
  have image (b : Bool) (X : M.Domain) : ∃ Y, ∀ z, M.mem z Y ↔ ∃ a, M.mem a X ∧ Fp_tag_d b ω a z := by
    let φ : Delta0BinarySchema 1 := { body := fp_tag0_m b (.bound 2) (.bound 1) .newest, delta0 := fp_tag0_delta_l .. }
    let ρ : Env M 1 := ⟨fun _ => ω, fun _ => ω⟩
    have sat a z : φ.toBinarySchema.denote ρ a z ↔ Fp_tag_d b ω a z := fp_tag0_sat_l hKP.1 _ _ _ _ _ hω
    obtain ⟨Y, spec⟩ := KP.d0_image_l hKP φ ρ X
      (fun a _ => (fp_tag_exists_l hKP hω b a).imp fun z hz => (sat a z).mpr hz)
      (fun _ _ z w hz hw => ((sat _ z).mp hz).unique_l hKP.1 ((sat _ w).mp hw))
    exact ⟨Y, fun z => (spec z).trans (exists_congr fun a => and_congr_right fun _ => sat a z)⟩
  obtain ⟨X, hx⟩ := image false x
  obtain ⟨Y, hy⟩ := image true y
  obtain ⟨p, hp⟩ := KP.exists_unionOfTwo hKP X Y
  exact ⟨p, fun z => (hp z).trans (or_congr (hx z) (hy z))⟩

theorem fp_pair0_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω x y p : Term d)
    (hω : M.IsInductive (ω.eval ρ)) :
    Formula.satisfies ρ (fp_pair0_m ω x y p) ↔ Fp_pair_d (ω.eval ρ) (x.eval ρ) (y.eval ρ) (p.eval ρ) := by
  have read (a z : M.Domain) (b : Bool) (t u : Term (d+2)) :=
    fp_tag0_sat_l hKP.1 ((ρ.push a).push z) b ω.weaken.weaken t u
      (by simpa only [Definitional.Term.eval_weaken] using hω)
  simp only [fp_pair0_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_existsMem_iff, read, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨bound, left, right⟩ z
    refine ⟨bound z, ?_⟩
    rintro (⟨a, ha, tag⟩ | ⟨b, hb, tag⟩)
    · obtain ⟨z', hz', tag'⟩ := left a ha
      exact tag'.unique_l hKP.1 tag ▸ hz'
    · obtain ⟨z', hz', tag'⟩ := right b hb
      exact tag'.unique_l hKP.1 tag ▸ hz'
  · intro pair
    refine ⟨fun z => (pair z).mp, fun a ha => ?_, fun b hb => ?_⟩
    · obtain ⟨z, tag⟩ := fp_tag_exists_l hKP hω false a
      exact ⟨z, (pair z).mpr (Or.inl ⟨a, ha, tag⟩), tag⟩
    · obtain ⟨z, tag⟩ := fp_tag_exists_l hKP hω true b
      exact ⟨z, (pair z).mpr (Or.inr ⟨b, hb, tag⟩), tag⟩

theorem Fp_pair_d.injective_l (hKP : M.Models KP) {ω x y u v p : M.Domain}
    (hω : M.IsInductive ω) (ordinals : ∀ n, M.mem n ω → M.IsOrdinal n)
    (h : Fp_pair_d ω x y p) (k : Fp_pair_d ω u v p) : x = u ∧ y = v := by
  have recover (b : Bool) (a z : M.Domain) (tag : Fp_tag_d b ω a z)
      {x y : M.Domain} (pair : Fp_pair_d ω x y p) (hz : M.mem z p) : M.mem a (if b then y else x) := by
    rcases (pair z).mp hz with ⟨r, hr, ht⟩ | ⟨r, hr, ht⟩
    · obtain ⟨rfl, rfl⟩ := tag.injective_l hKP.1 hω ordinals ht
      exact hr
    · obtain ⟨rfl, rfl⟩ := tag.injective_l hKP.1 hω ordinals ht
      exact hr
  have sub (b : Bool) {x y u v : M.Domain} (pair : Fp_pair_d ω x y p) (pair' : Fp_pair_d ω u v p) :
      M.MemberSubset (if b then y else x) (if b then v else u) := by
    intro a ha
    obtain ⟨z, tag⟩ := fp_tag_exists_l hKP hω b a
    apply recover b a z tag pair'
    apply (pair z).mpr
    cases b
    · exact Or.inl ⟨a, ha, tag⟩
    · exact Or.inr ⟨a, ha, tag⟩
  exact ⟨hKP.1.eq_of_same_members x u (fun a => ⟨sub false h k a, sub false k h a⟩),
    hKP.1.eq_of_same_members y v (fun a => ⟨sub true h k a, sub true k h a⟩)⟩

def Fp_d (p x y : M.Domain) : Prop := ∃ ω, M.IsOmega ω ∧ Fp_pair_d ω x y p

theorem fp_fixed_l (hE : Extensional M) {ω p x y : M.Domain} (hω : M.IsOmega ω) :
    Fp_d p x y ↔ Fp_pair_d ω x y p := by
  refine ⟨?_, fun h => ⟨ω, hω, h⟩⟩
  rintro ⟨Ω, hΩ, h⟩
  have eq := hE.eq_of_same_members Ω ω (fun z => ⟨hΩ.2 ω hω.1 z, hω.2 Ω hΩ.1 z⟩)
  exact eq ▸ h

theorem fp_code_sat_l (hE : Extensional M) {d} (ρ : Env M d) (p x y : Term d) :
    Formula.satisfies ρ (FlatPairing.code p x y) ↔ Fp_d (p.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [FlatPairing.code, Fp_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOmega_iff, fp_pair_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

/-- 原默认配对约定的实际实例；ω 只在存在命题内取见证。 -/
def fp_interpretation_l (hM : M.Models KPi) : FlatPairing.convention.Interpretation M where
  Codes := Fp_d
  realizes := fp_code_sat_l (KPi.models_iff_l.mp hM).1.1
  total x y := by
    obtain ⟨ω, hω, _⟩ := KPi.exists_omega_l hM
    obtain ⟨p, hp⟩ := fp_pair_exists_l (KPi.models_iff_l.mp hM).1 hω.1 x y
    exact ⟨p, ω, hω, hp⟩
  unique := by
    rintro p q x y ⟨ω, hω, hp⟩ ⟨Ω, hΩ, hq⟩
    have eq := (KPi.models_iff_l.mp hM).1.1.eq_of_same_members Ω ω
      (fun z => ⟨hΩ.2 ω hω.1 z, hω.2 Ω hΩ.1 z⟩)
    subst Ω
    exact hp.unique_l (KPi.models_iff_l.mp hM).1.1 hq
  injective := by
    rintro p x y u v ⟨ω, hω, hp⟩ ⟨Ω, hΩ, hq⟩
    have eq := (KPi.models_iff_l.mp hM).1.1.eq_of_same_members Ω ω
      (fun z => ⟨hΩ.2 ω hω.1 z, hω.2 Ω hΩ.1 z⟩)
    subst Ω
    have hn := ((omega0_iff_l hM hω).mpr rfl).2
    exact hp.injective_l (KPi.models_iff_l.mp hM).1 hω.1 (fun n h => KPi.n0_ordinal_l hM (hn n h)) hq

end YesMetaZFC.SetTheory
