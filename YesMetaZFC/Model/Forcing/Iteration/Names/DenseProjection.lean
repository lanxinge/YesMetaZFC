import YesMetaZFC.Model.Forcing.Proper.Elementary.FirstPreimage
import YesMetaZFC.Model.Forcing.Internal.Reflection.Transitive
import YesMetaZFC.Model.Forcing.Proper.Master.Basic

/-! # 稠密集向前段的投影及内部见证

以所有前段上界刻画投影下界，公式只量化实际条件载体。这样在 H(χ) 中
反射投影集和稠密见证只需传递绝对性，不要求 H(χ) 满足 ZF。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def Prj_wit_d (M : SetTheory.Structure.{u}) (B R D V E r a s : M.Domain) : Prop :=
  M.mem s D ∧ M.mem s E ∧ Entry_d M s r V ∧
    ∀ b, M.mem b B → Entry_d M s b V → Entry_d M a b R

def prj_wit_m {n} (B R D V E r a s : Term n) : Formula 1 n :=
  .conj (.mem s D) (.conj (.mem s E) (.conj (entry_m s r V)
    (Formula.forallMem B (.imp (entry_m s.weaken .newest V.weaken) (entry_m a.weaken .newest R.weaken)))))
derive_free_closed prj_wit_m

theorem prj_wit_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R D V E r a s : Term n) :
    Formula.satisfies ρ (prj_wit_m B R D V E r a s) ↔
      Prj_wit_d M (B.eval ρ) (R.eval ρ) (D.eval ρ) (V.eval ρ) (E.eval ρ) (r.eval ρ) (a.eval ρ) (s.eval ρ) := by
  simp only [prj_wit_m, Prj_wit_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    entry_sat_l M hE, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, Definitional.Term.eval_weaken]
  rfl

def Prj_set_d (M : SetTheory.Structure.{u}) (B R D V E r Z : M.Domain) : Prop :=
  M.MemberSubset Z B ∧ ∀ a, M.mem a B →
    (M.mem a Z ↔ a ≠ B ∧ (¬ Cmp_d M D V D a r ∨ ∃ s, Prj_wit_d M B R D V E r a s))

def prj_case_m {n} (B R D V E r a : Term n) : Formula 1 n :=
  .conj (.neg (Formula.extensionalEq a B)) (.disj (.neg (cmp_m D V D a r))
    (.existsE (prj_wit_m B.weaken R.weaken D.weaken V.weaken E.weaken r.weaken a.weaken .newest)))
derive_free_closed prj_case_m

def prj_set_m {n} (B R D V E r Z : Term n) : Formula 1 n := .conj (Formula.subset Z B)
  (Formula.forallMem B (.iff (.mem .newest Z.weaken)
    (prj_case_m B.weaken R.weaken D.weaken V.weaken E.weaken r.weaken .newest)))
derive_free_closed prj_set_m

theorem prj_case_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R D V E r a : Term n) :
    Formula.satisfies ρ (prj_case_m B R D V E r a) ↔ a.eval ρ ≠ B.eval ρ ∧
      (¬ Cmp_d M (D.eval ρ) (V.eval ρ) (D.eval ρ) (a.eval ρ) (r.eval ρ) ∨
        ∃ s, Prj_wit_d M (B.eval ρ) (R.eval ρ) (D.eval ρ) (V.eval ρ) (E.eval ρ) (r.eval ρ) (a.eval ρ) s) := by
  simp only [prj_case_m, Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_disj_iff, cmp_sat_l M hE,
    Formula.satisfies_exists_iff, prj_wit_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem prj_set_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R D V E r Z : Term n) :
    Formula.satisfies ρ (prj_set_m B R D V E r Z) ↔
      Prj_set_d M (B.eval ρ) (R.eval ρ) (D.eval ρ) (V.eval ρ) (E.eval ρ) (r.eval ρ) (Z.eval ρ) := by
  simp only [prj_set_m, Prj_set_d, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    prj_case_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem prj_set_exists_l (hZF : M.Models ZF) (B R D V E r : M.Domain) : ∃ Z, Prj_set_d M B R D V E r Z := by
  let ρ₀ : Env M 3 := ((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push D
  let ρ : Env M 6 := ((ρ₀.push V).push E).push r
  let φ : UnarySchema 6 := { body := prj_case_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨Z, hZ⟩ := ZF.separation_exists_d hZF φ ρ B
  exact ⟨Z, (fun a ha => ((hZ a).mp ha).1), fun a ha =>
    (hZ a).trans ((and_iff_right ha).trans (prj_case_sat_l hZF.1 _ _ _ _ _ _ _ _))⟩

section Absolute
variable {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) {c H J}
  (hM : Smdl_d I c H J) (hJ : ∀ x y, M.PairMember I x y J ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
  (hH : M.TransitiveSet H)
local notation "L" => smdl_structure_l I (R := J) (And.left (And.right hM))
include hJ hH

theorem smem_cmp_l (B R z p q : (L).Domain) : Cmp_d L B R z p q ↔ Cmp_d M B.val R.val z.val p.val q.val := by
  constructor
  · rintro ⟨a, ha, haq⟩
    exact ⟨a.val, (smem_below_l I hM hJ hH B R z a p).mp ha, (smem_entry_l I hM hJ hH a q R).mp haq⟩
  · rintro ⟨a, ha, haq⟩
    let a' : (L).Domain := ⟨a, hH B.val B.property a ha.1⟩
    exact ⟨a', (smem_below_l I hM hJ hH B R z a' p).mpr ha, (smem_entry_l I hM hJ hH a' q R).mpr haq⟩

theorem smem_prj_wit_l (B R D V E r a s : (L).Domain) :
    Prj_wit_d L B R D V E r a s ↔ Prj_wit_d M B.val R.val D.val V.val E.val r.val a.val s.val := by
  unfold Prj_wit_d
  apply and_congr (smem_member_l I hM hJ s D)
  apply and_congr (smem_member_l I hM hJ s E)
  apply and_congr (smem_entry_l I hM hJ hH s r V)
  constructor
  · intro hh b hb hsb
    let b' : (L).Domain := ⟨b, hH B.val B.property b hb⟩
    exact (smem_entry_l I hM hJ hH a b' R).mp (hh b' ((smem_member_l I hM hJ b' B).mpr hb)
      ((smem_entry_l I hM hJ hH s b' V).mpr hsb))
  · intro hh b hb hsb
    exact (smem_entry_l I hM hJ hH a b R).mpr (hh b.val ((smem_member_l I hM hJ b B).mp hb)
      ((smem_entry_l I hM hJ hH s b V).mp hsb))

theorem smem_prj_case_l (B R D V E r a : (L).Domain) :
    (a ≠ B ∧ (¬ Cmp_d L D V D a r ∨ ∃ s, Prj_wit_d L B R D V E r a s)) ↔
    (a.val ≠ B.val ∧ (¬ Cmp_d M D.val V.val D.val a.val r.val ∨
      ∃ s, Prj_wit_d M B.val R.val D.val V.val E.val r.val a.val s)) := by
  apply and_congr (not_congr ⟨congrArg Subtype.val, fun h => Subtype.ext h⟩)
  apply or_congr (not_congr (smem_cmp_l I hM hJ hH D V D a r))
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s.val, (smem_prj_wit_l I hM hJ hH B R D V E r a s).mp hs⟩
  · rintro ⟨s, hs⟩
    let s' : (L).Domain := ⟨s, hH D.val D.property s hs.1⟩
    exact ⟨s', (smem_prj_wit_l I hM hJ hH B R D V E r a s').mpr hs⟩

theorem smem_prj_set_l (B R D V E r Z : (L).Domain) :
    Prj_set_d L B R D V E r Z ↔ Prj_set_d M B.val R.val D.val V.val E.val r.val Z.val := by
  have hh (a : (L).Domain) := smem_prj_case_l I hM hJ hH B R D V E r a
  constructor
  · rintro ⟨hz, hf⟩
    refine ⟨(smem_subset_l I hM hJ hH Z B).mp hz, fun a ha => ?_⟩
    let a' : (L).Domain := ⟨a, hH B.val B.property a ha⟩
    exact (smem_member_l I hM hJ a' Z).symm.trans
      ((hf a' ((smem_member_l I hM hJ a' B).mpr ha)).trans (hh a'))
  · rintro ⟨hz, hf⟩
    exact ⟨(smem_subset_l I hM hJ hH Z B).mpr hz, fun a ha => (smem_member_l I hM hJ a Z).trans
      ((hf a.val ((smem_member_l I hM hJ a B).mp ha)).trans (hh a).symm)⟩
end Absolute

variable (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

/-- 投影稠密集和其中的旧条件见证均在同一个 N 内取得。 -/
theorem selem_prj_set_l {ω χ H c J d N S B R D V E r}
    (hω : M.IsOmega ω) (hχ : M.IsLimitOrdinal χ) (hH : H_d I χ H)
    (hJ : ∀ x y, M.PairMember I x y J ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d I c d H J N S) (hElem : Selem_d I ω c d)
    (hB : M.mem B N) (hR : M.mem R N) (hD : M.mem D N) (hV : M.mem V N) (hE : M.mem E N) (hr : M.mem r N) :
    (∃ Z, M.mem Z N ∧ Prj_set_d M B R D V E r Z) ∧
    ∀ a, M.mem a N → (∃ s, Prj_wit_d M B R D V E r a s) → ∃ s, M.mem s N ∧ Prj_wit_d M B R D V E r a s := by
  let L := smdl_structure_l I (R := J) hSub.source.2.1
  let Q := smdl_structure_l I (R := S) hSub.target.2.1
  let f : Fin 6 → M.Domain := Fin.cases r (Fin.cases E (Fin.cases V (Fin.cases D (Fin.cases R (fun _ => B)))))
  have hf : ∀ i, M.mem (f i) N := Fin.cases hr (Fin.cases hE (Fin.cases hV (Fin.cases hD (Fin.cases hR (fun _ => hB)))))
  let ρ : Env L 6 := ⟨fun i => ⟨f i, hSub.subset _ (hf i)⟩, fun _ => ⟨B, hSub.subset _ hB⟩⟩
  let η : Env Q 6 := ⟨fun i => ⟨f i, hf i⟩, fun _ => ⟨B, hB⟩⟩
  have htr := ZF.h_transitive_l I hZF hH
  have hLE := smem_ext_l I hSub.source hJ htr hZF.1
  constructor
  · let φ : UnarySchema 6 := { body := prj_set_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
    have hφ (Z : L.Domain) : φ.denote ρ Z ↔ Prj_set_d M B R D V E r Z.val :=
      (prj_set_sat_l hLE _ _ _ _ _ _ _ _).trans (smem_prj_set_l I hSub.source hJ htr _ _ _ _ _ _ Z)
    obtain ⟨Z, hZ⟩ := prj_set_exists_l hZF B R D V E r
    have hZH := ZF.h_subsets_l I hZF hχ hH (hSub.subset B hB) Z hZ.1
    obtain ⟨Z', hZ'⟩ := selem_witness_l I hZF hω hSub hElem φ ρ η (fun _ => rfl)
      ⟨⟨Z, hZH⟩, (hφ _).mpr hZ⟩
    exact ⟨Z'.val, Z'.property, (hφ _).mp hZ'⟩
  · intro a ha ⟨s, hs⟩
    let φ : UnarySchema 7 := { body := prj_wit_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
    let a' : L.Domain := ⟨a, hSub.subset a ha⟩
    have hφ (s : L.Domain) : φ.denote (ρ.push a') s ↔ Prj_wit_d M B R D V E r a s.val :=
      (prj_wit_sat_l hLE _ _ _ _ _ _ _ _ _).trans (smem_prj_wit_l I hSub.source hJ htr _ _ _ _ _ _ a' s)
    have hsH := htr D (hSub.subset D hD) s hs.1
    obtain ⟨s', hs'⟩ := selem_witness_l I hZF hω hSub hElem φ (ρ.push a') (η.push ⟨a, ha⟩) (Fin.cases rfl (fun _ => rfl))
      ⟨⟨s, hsH⟩, (hφ _).mpr hs⟩
    exact ⟨s'.val, s'.property, (hφ _).mp hs'⟩

end YesMetaZFC.Model.Forcing.Internal
