import YesMetaZFC.SetTheory.Descriptive.Projective.Section
import YesMetaZFC.SetTheory.Descriptive.Normal.Closed

/-! # 实际通用闭集

实数 p 以第 E(s) 坐标是否为零编码前缀 s；截面由全部获准前缀的分支组成。
任一闭集的规范树均有这样的实际参数实数。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Uv_d (A E z p x : M.Domain) : Prop := ∀ s, M.mem s A → M.MemberSubset s x → ¬ Nv_d I E p s z
def uv_m {d} (A E z p x : Term d) : Formula 1 d := Formula.forallMem A
  (.imp (Formula.subset .newest x.weaken) (.neg (nv_m (𝒞 := 𝒞) E.weaken p.weaken .newest z.weaken)))
derive_free_closed uv_m
theorem uv_sat_l {d} (ρ : Env M d) (A E z p x : Term d) :
    Formula.satisfies ρ (uv_m (𝒞 := 𝒞) A E z p x) ↔ Uv_d I (A.eval ρ) (E.eval ρ) (z.eval ρ) (p.eval ρ) (x.eval ρ) := by
  simp only [uv_m, Uv_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_neg_iff, nv_sat_l I, Definitional.Term.eval_weaken]; rfl

def Uc_d (A B J E z q : M.Domain) : Prop := ∃ p x, M.mem p B ∧ M.mem x B ∧ Rp_d I J p x q ∧ Uv_d I A E z p x
def uc_m {d} (A B J E z q : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (.mem (.bound 1) B.weaken.weaken) (.conj (.mem .newest B.weaken.weaken) (.conj
  (rp_m (𝒞 := 𝒞) J.weaken.weaken (.bound 1) .newest q.weaken.weaken)
  (uv_m (𝒞 := 𝒞) A.weaken.weaken E.weaken.weaken z.weaken.weaken (.bound 1) .newest)))))
derive_free_closed uc_m
theorem uc_sat_l {d} (ρ : Env M d) (A B J E z q : Term d) :
    Formula.satisfies ρ (uc_m (𝒞 := 𝒞) A B J E z q) ↔
      Uc_d I (A.eval ρ) (B.eval ρ) (J.eval ρ) (E.eval ρ) (z.eval ρ) (q.eval ρ) := by
  simp only [uc_m, Uc_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, rp_sat_l I, uv_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem uc_closed_l (hZF : M.Models ZF) {ω A B J} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (E z : M.Domain) :
    ∃ C, Cl_d A B C ∧ ∀ q, M.mem q C ↔ M.mem q B ∧ Uc_d I A B J E z q := by
  classical
  let ρ : Env M 5 := ((((⟨fun _ => A, fun _ => A⟩ : Env M 1).push B).push J).push E).push z
  let φ : UnarySchema 5 := { body := uc_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨C, hC'⟩ := ZF.separation_exists_d hZF φ ρ B
  have hC q : M.mem q C ↔ M.mem q B ∧ Uc_d I A B J E z q :=
    (hC' q).trans (and_congr_right fun _ => uc_sat_l I _ _ _ _ _ _ _)
  obtain ⟨U, hU⟩ := cm_exists_l (ZF.modelsKP hZF) B C
  refine ⟨C, ⟨fun q hq => ((hC q).mp hq).1, U, hU, ⟨fun q hq => ((hU q).mp hq).1, ?_⟩⟩, hC⟩
  intro q hq
  obtain ⟨hqB, hqC⟩ := (hU q).mp hq
  obtain ⟨p, x, hpf, hxf, pair⟩ := rp_decode_l I hZF hJ ((hB.2 q).mp hqB)
  obtain ⟨s, hs, hsx, bad⟩ : ∃ s, M.mem s A ∧ M.MemberSubset s x ∧ Nv_d I E p s z := by
    exact Classical.byContradiction (fun h => hqC ((hC q).mpr ⟨hqB, p, x, (hB.2 p).mpr hpf, (hB.2 x).mpr hxf,
      pair, fun s hs sub hb => h ⟨s, hs, sub, hb⟩⟩))
  obtain ⟨n, t, u, hn, ht, hu, obs⟩ := no_and_l I hZF hB.1 hxf hpf
    (no_sub_l I hZF hB.1 hA hxf hpf hs hsx) (no_nv_l I hZF hB.1 hxf hpf bad)
  have htf := ht.isSetFunctionFromTo hxf (hB.1.transitive (ZF.modelsKP hZF) n hn)
  have huf := hu.isSetFunctionFromTo hpf (hB.1.transitive (ZF.modelsKP hZF) n hn)
  obtain ⟨r, hrf, rp⟩ := rp_exists_l I hZF hJ huf htf
  refine ⟨r, (hA r).mpr ⟨n, hn, hrf⟩, (rp_subset_l I hJ huf htf rp pair).mpr
    ⟨(ds_restrict_iff_l I huf hpf.1).mp hu, (ds_restrict_iff_l I htf hxf.1).mp ht⟩, fun q' hq' hrq => ?_⟩
  apply (hU q').mpr
  refine ⟨hq', fun hc => ?_⟩
  obtain ⟨_, p', x', _, _, pair', val⟩ := (hC q').mp hc
  have sub := (rp_subset_l I hJ huf htf rp pair').mp hrq
  have ob := obs x' p' sub.2 sub.1
  exact val s hs ob.1 ob.2

theorem universal_closed_l (hZF : M.Models ZF) {ω A B J} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J) :
    ∃ C, Cl_d A B C ∧ ∀ K, Cl_d A B K → ∃ p, Sect_d I B J C p K := by
  classical
  obtain ⟨E, he⟩ := ha
  obtain ⟨z, hz, hzω⟩ := hB.1.1.1
  obtain ⟨o, ho, hoω⟩ := hB.1.1.2 z hzω
  have noz : o ≠ z := fun e => hz z (e ▸ ho.predecessor_mem)
  obtain ⟨C, hc, ec⟩ := uc_closed_l I hZF hB hA hJ E z
  refine ⟨C, hc, fun K hk => ?_⟩
  obtain ⟨T, _, body⟩ := (closed_tree_l (ZF.modelsKP hZF)).mp hk
  let ρ : Env M 3 := ((⟨fun _ => T, fun _ => T⟩ : Env M 1).push z).push o
  let φ : BinarySchema 3 := {
    body := .disj (.conj (.mem (.bound 1) (.bound 4)) (Formula.extensionalEq .newest (.bound 2)))
      (.conj (.neg (.mem (.bound 1) (.bound 4))) (Formula.extensionalEq .newest (.bound 3))) }
  have hp s v : φ.denote ρ s v ↔ (M.mem s T ∧ v = o) ∨ (¬ M.mem s T ∧ v = z) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_neg_iff]; rfl
  obtain ⟨G, hg, eg⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := A) (target := ω)
    (fun s _ => by
      by_cases hs : M.mem s T
      · exact ⟨o, (hp s o).mpr (Or.inl ⟨hs, rfl⟩)⟩
      · exact ⟨z, (hp s z).mpr (Or.inr ⟨hs, rfl⟩)⟩)
    (by
      intro s _ v w hv hw
      rcases (hp s v).mp hv with ⟨ht, hv⟩ | ⟨ht, hv⟩ <;> rcases (hp s w).mp hw with ⟨hu, hw⟩ | ⟨hu, hw⟩
      · exact hv.trans hw.symm
      · exact (hu ht).elim
      · exact (ht hu).elim
      · exact hv.trans hw.symm)
    (fun s v _ hv => ((hp s v).mp hv).elim (fun h => h.2.symm ▸ hoω) (fun h => h.2.symm ▸ hzω))
  obtain ⟨p, hpf, ep⟩ := nv_encode_l I hZF he hg hzω
  have zero s (hs : M.mem s A) : Nv_d I E p s z ↔ ¬ M.mem s T := by
    refine (ep s z hs).trans (((eg s z).trans (and_congr_right fun _ => hp s z)).trans ⟨?_, ?_⟩)
    · exact fun h => h.2.elim (fun h => (noz h.2.symm).elim) And.left
    · exact fun h => ⟨hs, Or.inr ⟨h, rfl⟩⟩
  refine ⟨p, (hB.2 p).mpr hpf, fun x q hx pair => ?_⟩
  have hxf := (hB.2 x).mp hx
  have hq := (hB.2 q).mpr (rp_type_l I hZF hJ hpf hxf pair)
  have value : Uv_d I A E z p x ↔ Branch_d A T x :=
    ⟨fun h s hs sub => Classical.byContradiction (fun hn => h s hs sub ((zero s hs).mpr hn)),
      fun h s hs sub hz => (zero s hs).mp hz (h s hs sub)⟩
  refine (ec q).trans ⟨?_, ?_⟩
  · rintro ⟨_, p', x', hp', hx', pair', val⟩
    obtain ⟨ep, ex⟩ := rp_injective_l I hZF.1 hJ ((hB.2 p').mp hp') ((hB.2 x').mp hx') hpf hxf pair' pair
    subst p' x'
    exact (body x).mpr ⟨hx, value.mp val⟩
  · intro hxK
    exact ⟨hq, p, x, (hB.2 p).mpr hpf, hx, pair, value.mpr ((body x).mp hxK).2⟩

end YesMetaZFC.SetTheory.Descriptive
