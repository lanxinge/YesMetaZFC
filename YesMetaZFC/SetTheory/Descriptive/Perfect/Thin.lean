import YesMetaZFC.SetTheory.Descriptive.Perfect.Derivative
import YesMetaZFC.SetTheory.Card.OrdinalImage

/-! # 导集消失时的可数性

每个投影实数都有一个首次丧失分裂能力的前缀。同一前缀的消失阶段唯一，
且此阶段至多容纳一个投影实数，故这些前缀给出实际可数编号。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem sp_of_two_l (hZF : M.Models ZF) {ω A B J U q x v} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hq : M.mem q A)
    (hx : M.mem x B) (hv : M.mem v B) (ax : As_d I A B J U q x) (av : As_d I A B J U q v) (ne : x ≠ v) : Sp_d I ω J U q := by
  obtain ⟨y, p, hy, hp, pr, path, hqp⟩ := ax
  obtain ⟨w, r, hw, hr, rr, rpath, hqr⟩ := av
  have xf := (hB.2 x).mp hx
  have vf := (hB.2 v).mp hv
  have pf := (hB.2 p).mp hp
  have rf := (hB.2 r).mp hr
  obtain ⟨i, a, b, hi, hia, hib, hab⟩ := ds_differ_l I hZF.1 xf vf ne
  obtain ⟨c, hc, hic⟩ := ((hB.2 y).mp hy).2.2 i hi
  obtain ⟨d, hd, hid⟩ := ((hB.2 w).mp hw).2.2 i hi
  obtain ⟨j, _, hj⟩ := np_total_l I hJ (xf.output_mem_of_pairMember hia) hc
  obtain ⟨k, _, hk⟩ := np_total_l I hJ (vf.output_mem_of_pairMember hib) hd
  have pairs := no_and_l I hZF hB.1 pf rf
    (no_pair_l I hZF hB.1 pf rf false ((pr.2 i j).mpr ⟨a, c, hia, hic, hj⟩))
    (no_pair_l I hZF hB.1 pf rf true ((rr.2 i k).mpr ⟨b, d, hib, hid, hk⟩))
  obtain ⟨n, s, t, hn, hs, ht, obs⟩ := no_sub_l I hZF hB.1 hA rf pf hq hqr
  have back : No_d I ω p r (fun _ t => M.MemberSubset q t) := ⟨n, t, s, hn, ht, hs, fun _ _ h h' => obs _ _ h' h⟩
  obtain ⟨n, s, t, hn, hs, ht, obs⟩ := no_and_l I hZF hB.1 pf rf pairs
    (no_and_l I hZF hB.1 pf rf (no_sub_l I hZF hB.1 hA pf rf hq hqp) back)
  have sf := hs.isSetFunctionFromTo pf (hB.1.transitive hZF n hn)
  have tf := ht.isSetFunctionFromTo rf (hB.1.transitive hZF n hn)
  have ob := obs s t (fun _ => id) (fun _ => id)
  obtain ⟨s₀, s₁, hs₀, hs₁, ps⟩ := rp_decode_l I hZF hJ sf
  obtain ⟨t₀, t₁, ht₀, ht₁, pt⟩ := rp_decode_l I hZF hJ tf
  obtain ⟨a', c', ha', _, hc'⟩ := (ps.2 i j).mp ob.1.1
  obtain ⟨b', d', hb', _, hd'⟩ := (pt.2 i k).mp ob.1.2
  have ea := (np_injective_l I hJ hc' hj).1
  have eb := (np_injective_l I hJ hd' hk).1
  exact ⟨path q hq hqp, s, t,
    path s ((hA s).mpr ⟨n, hn, sf⟩) ((ds_restrict_iff_l I sf pf.1).mp hs),
    rpath t ((hA t).mpr ⟨n, hn, tf⟩) ((ds_restrict_iff_l I tf rf.1).mp ht), ob.2.1, ob.2.2,
    s₀, s₁, t₀, t₁, ⟨n, hn, hs₀, hs₁, ps⟩, ⟨n, hn, ht₀, ht₁, pt⟩,
    i, a', b', ha', hb', fun e => hab (ea.symm.trans (e.trans eb))⟩

def Thin_d (ω A B J T s x : M.Domain) : Prop := ∃ α U,
  Sd_d I ω J T α U ∧ M.mem s U ∧ ¬ Sp_d I ω J U s ∧ M.mem x B ∧ As_d I A B J U s x
def thin_m {d} (ω A B J T s x : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (sd_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken T.weaken.weaken (.bound 1) .newest) (.conj
  (.mem s.weaken.weaken .newest) (.conj (.neg (sp_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken .newest s.weaken.weaken)) (.conj
  (.mem x.weaken.weaken B.weaken.weaken) (as_m (𝒞 := 𝒞) A.weaken.weaken B.weaken.weaken J.weaken.weaken .newest s.weaken.weaken x.weaken.weaken))))))
derive_free_closed thin_m
theorem thin_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J T s x : Term d) :
    Formula.satisfies ρ (thin_m (𝒞 := 𝒞) ω A B J T s x) ↔
      Thin_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (T.eval ρ) (s.eval ρ) (x.eval ρ) := by
  simp only [thin_m, Thin_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    sd_sat_l I hE, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, sp_sat_l I hE,
    as_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem thin_unique_l (hZF : M.Models ZF) {ω A B J T s x y} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hs : M.mem s A)
    (hx : Thin_d I ω A B J T s x) (hy : Thin_d I ω A B J T s y) : x = y := by
  obtain ⟨α, U, hu, hsU, nu, hx, ax⟩ := hx
  obtain ⟨β, V, hv, hsV, nv, hy, ay⟩ := hy
  have ho {α U} (h : Sd_d I ω J T α U) : M.IsOrdinal α := h.elim fun _ h => h.1.1.1
  have e : α = β := by
    rcases Structure.IsOrdinal.trichotomy hZF.1 (ho hu) (ho hv) (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) α β) with e | e | e
    · exact hZF.1.eq_of_same_members α β e
    · exact (nu (((sd_unfold_l I hZF hv s).mp hsV).2 α U e hu)).elim
    · exact (nv (((sd_unfold_l I hZF hu s).mp hsU).2 β V e hv)).elim
  subst β
  have e := sd_unique_l I hZF hv hu
  subst V
  exact Classical.byContradiction (fun ne => nu (sp_of_two_l I hZF hB hA hJ hs hx hy ax ay ne))

theorem thin_exists_l (hZF : M.Models ZF) {ω A B J T K α U x} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hT : Atree_d I A B J T K) (hu : Sd_d I ω J T α U)
    (he : ∀ s, ¬ M.mem s U) (hx : M.mem x K) : ∃ s, M.mem s A ∧ Thin_d I ω A B J T s x := by
  classical
  obtain ⟨z, hz, hzω⟩ := hB.1.1.1
  obtain ⟨hxB, y, p, hy, hp, pair, path, _⟩ := (as_root_l I hT hz x).mp hx
  have ha : M.IsOrdinal α := hu.elim fun _ h => h.1.1.1
  obtain ⟨δ, hd⟩ := KP.exists_successor (ZF.modelsKP hZF) α
  have ho := KP.successor_isOrdinal (ZF.modelsKP hZF) ha hd
  let ρ : Env M 5 := ((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push J).push T).push A).push p
  let φ : UnarySchema 5 := { body := .existsE (.conj
    (sd_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 1) .newest)
    (.neg (branch_m (.bound 3) .newest (.bound 2)))) }
  have hv β : φ.denote ρ β ↔ ∃ V, Sd_d I ω J T β V ∧ ¬ Branch_d A V p := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      sd_sat_l I hZF.1, Formula.satisfies_neg_iff, branch_sat_l]; rfl
  obtain ⟨D, hd'⟩ := ZF.separation_exists_d hZF φ ρ δ
  have hD β := (hd' β).trans (and_congr_right fun _ => hv β)
  have bad : ¬ Branch_d A U p := fun h => he z (h z ((hA z).mpr ⟨z, hzω, ds_empty_fun_l I hz⟩) (fun a h => (hz a h).elim))
  obtain ⟨β, hb, least⟩ := ho.wellOrder.least D (fun β hb => ((hD β).mp hb).1) ⟨α, (hD α).mpr ⟨hd.predecessor_mem, U, hu, bad⟩⟩
  obtain ⟨hbδ, V, hv, bad⟩ := (hD β).mp hb
  obtain ⟨s, hs, hsp, hn⟩ : ∃ s, M.mem s A ∧ M.MemberSubset s p ∧ ¬ M.mem s V := by
    exact Classical.byContradiction (fun h => bad (fun s hs sub => Classical.byContradiction (fun hn => h ⟨s, hs, sub, hn⟩)))
  obtain ⟨γ, W, hγβ, hw, ns⟩ : ∃ γ W, M.mem γ β ∧ Sd_d I ω J T γ W ∧ ¬ Sp_d I ω J W s := by
    exact Classical.byContradiction (fun h => hn ((sd_unfold_l I hZF hv s).mpr ⟨path s hs hsp,
      fun γ W hγ hw => Classical.byContradiction (fun ns => h ⟨γ, W, hγ, hw, ns⟩)⟩))
  have good : Branch_d A W p := by
    apply Classical.byContradiction
    intro no
    rcases least γ ((hD γ).mpr ⟨ho.transitive β hbδ γ hγβ, W, hw, no⟩) with e | e
    · exact KP.mem_irrefl_d (ZF.modelsKP hZF) γ (hZF.1.eq_of_same_members β γ e ▸ hγβ)
    · exact KP.mem_irrefl_d (ZF.modelsKP hZF) β ((ho.mem hbδ).transitive γ hγβ β e)
  exact ⟨s, hs, γ, W, hw, good s hs hsp, ns, hxB, y, p, hy, hp, pair, good, hsp⟩

theorem sd_empty_countable_l (hZF : M.Models ZF) {ω A B J T K α U} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hc : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hT : Atree_d I A B J T K) (hu : Sd_d I ω J T α U) (he : ∀ s, ¬ M.mem s U) :
    M.CardinalLessOrEqual I K ω := by
  let ρ : Env M 6 := (((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J).push T).push K
  let φ : BinarySchema 6 := {
    body := .conj (.mem .newest (.bound 2))
      (thin_m (𝒞 := 𝒞) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest) }
  have hp s x : φ.denote ρ s x ↔ M.mem x K ∧ Thin_d I ω A B J T s x := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, thin_sat_l I hZF.1]; rfl
  let ψ : UnarySchema 6 := { body := .existsE φ.body }
  obtain ⟨D, hd'⟩ := ZF.separation_exists_d hZF ψ ρ A
  have hd s : M.mem s D ↔ M.mem s A ∧ ∃ x, φ.denote ρ s x := by
    simpa only [ψ, Formula.satisfies_exists_iff, BinarySchema.denote] using hd' s
  obtain ⟨F, hf, ef⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := K)
    (fun s hs => ((hd s).mp hs).2)
    (fun s hs x y hx hy => thin_unique_l I hZF hB hA hJ ((hd s).mp hs).1 ((hp s x).mp hx).2 ((hp s y).mp hy).2)
    (fun s x _ hx => ((hp s x).mp hx).1)
  obtain ⟨E, hE⟩ := hc
  obtain ⟨G, hg⟩ := ZF.exists_inclusionInjection hZF I (fun s hs => ((hd s).mp hs).1)
  apply ZF.ordinal_image_bound_l I hZF (hB.1.isOrdinal hZF) (ZF.exists_compositionInjection hZF I hg hE) hf
  intro x hx
  obtain ⟨s, hs, ht⟩ := thin_exists_l I hZF hB hA hT hu he hx
  have hsD := (hd s).mpr ⟨hs, x, (hp s x).mpr ⟨hx, ht⟩⟩
  exact ⟨s, hsD, (ef s x).mpr ⟨hsD, (hp s x).mpr ⟨hx, ht⟩⟩⟩

end YesMetaZFC.SetTheory.Descriptive
