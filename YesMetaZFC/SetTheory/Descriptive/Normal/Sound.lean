import YesMetaZFC.SetTheory.Descriptive.Normal.Syntax

/-! # 闭证书的可靠性

证书与已有内部求值逐节点相符。比较性质是实际原公式，使用内部良基归纳，
不把非标准树当成外部良基树处理。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem nf_nodiff_l (hZF : M.Models ZF) {ω n s x} (hω : M.IsOmega ω) (hn : M.mem n ω)
    (hs : M.IsSetFunctionFromTo I s n ω) (hx : M.IsSetFunctionFromTo I x ω ω)
    (h : ∀ j, ¬ Diff_d I s x j) : M.MemberSubset s x := by
  intro p hp
  obtain ⟨i, a, hc⟩ := hs.1.1 p hp
  obtain ⟨b, _, hb⟩ := hx.2.2 i (hω.transitive hZF n hn i (hs.input_mem_of_pairMember ⟨p, hc, hp⟩))
  have e : a = b := Classical.byContradiction (fun e => h i ⟨a, b, ⟨p, hc, hp⟩, hb, e⟩)
  obtain ⟨q, hq, hqx⟩ := hb
  exact (I.unique (e ▸ hc) hq).symm ▸ hqx

theorem nb_agree_l (hZF : M.Models ZF) {ω A T R N F E z x w V} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hc : Btree_d I ω A A T R N F)
    (he : M.IsSetFunctionFromTo I E T ω) (hx : M.IsSetFunctionFromTo I x ω ω)
    (hw : M.IsSetFunctionFromTo I w ω ω) (hn : ¬ Nb_d I T R N F E z x w)
    (hv : Bsem_d I T R N F x V) : ∀ a, M.mem a T → ∀ v, Nv_d I E w a v → (M.mem a V ↔ v ≠ z) := by
  classical
  let ρ : Env M 4 := (((⟨fun _ => E, fun _ => E⟩ : Env M 1).push w).push z).push V
  let φ : UnarySchema 4 := {
    body := .forallE (.imp (nv_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 1) .newest)
      (.iff (.mem (.bound 1) (.bound 2)) (.neg (Formula.extensionalEq .newest (.bound 3))))) }
  have hp a : φ.denote ρ a ↔ ∀ v, Nv_d I E w a v → (M.mem a V ↔ v ≠ z) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      nv_sat_l I, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  have all := wf_rel_ind_l hZF hc.wf φ ρ (fun a ha ih => (hp a).mpr (by
    intro v hav
    by_cases hf : ∃ s, M.PairMember I a s F
    · obtain ⟨s, hs⟩ := hf
      have leaf := hc.leaf a s hs
      refine (bsem_leaf_l I hv hc.leaf_fn ha leaf.2.2.1 hs).trans ⟨?_, ?_⟩
      · exact fun hsx e => hn (Or.inr (Or.inl ⟨a, s, v, hs, hav, Or.inl ⟨e, hsx⟩⟩))
      · intro hne
        obtain ⟨n, hnω, hsF⟩ := (hA s).mp leaf.2.1
        exact nf_nodiff_l I hZF hω hnω hsF hx (fun j hd =>
          hn (Or.inr (Or.inl ⟨a, s, v, hs, hav, Or.inr ⟨hne, j, hd⟩⟩)))
    · by_cases haN : M.mem a N
      · obtain ⟨b, hb, hba, hu⟩ := hc.neg a haN
        obtain ⟨u, _, hbu⟩ := nv_total_l I he hw hb
        have ib := (hp b).mp (ih b hb hba) u hbu
        have wrong : ¬ (v = z ↔ u = z) := fun h => hn (Or.inr (Or.inr (Or.inl ⟨a, b, v, u, haN, hba, hav, hbu, h⟩)))
        have eqn : v ≠ z ↔ u = z := ⟨fun h => Classical.byContradiction (fun h' => wrong (iff_of_false h h')),
          fun h e => wrong (iff_of_true e h)⟩
        have val : M.mem a V ↔ u = z := by
          simpa only [Classical.not_not] using (bsem_neg_l I hv ha haN hf hb hba hu).trans (not_congr ib)
        exact val.trans eqn.symm
      · have hu : Buni_d I N F a := ⟨haN, hf⟩
        have bad (h : Nu_d I T R E z a v w) := hn (Or.inr (Or.inr (Or.inr ⟨a, v, hu, hav, h⟩)))
        refine (bsem_union_l I hv ha haN hf).trans ⟨?_, ?_⟩
        · rintro ⟨b, hb, hba, hbV⟩ e
          obtain ⟨u, _, hbu⟩ := nv_total_l I he hw hb
          exact bad (Or.inl ⟨e, b, u, hb, hba, hbu, ((hp b).mp (ih b hb hba) u hbu).mp hbV⟩)
        · intro hne
          have sel : Ns_d I T R E a v := Classical.byContradiction (fun h => bad (Or.inr (Or.inl ⟨hne, h⟩)))
          obtain ⟨b, j, hb, hba, hbj, hj⟩ := sel
          obtain ⟨u, _, hbu⟩ := nv_total_l I he hw hb
          have hne' : u ≠ z := fun e => bad (Or.inr (Or.inr ⟨b, j, hb, hba, hbj, hj, e ▸ hbu⟩))
          exact ⟨b, hb, hba, ((hp b).mp (ih b hb hba) u hbu).mpr hne'⟩))
  exact fun a ha => (hp a).mp (all a ha)

theorem nb_sound_l (hZF : M.Models ZF) {ω A c T R N F E z x w} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hc : Btree_d I ω A A T R N F) (hpack : Bpack_d I c T R N F)
    (he : M.IsSetFunctionFromTo I E T ω) (hz : ∀ p, ¬ M.mem p z)
    (hx : M.IsSetFunctionFromTo I x ω ω) (hw : M.IsSetFunctionFromTo I w ω ω)
    (hn : ¬ Nb_d I T R N F E z x w) : Bsat_d I ω A A c x := by
  obtain ⟨e, he0, het⟩ := hc.root
  have hzT := hZF.1.eq_of_same_members e z (fun p => iff_of_false (he0 p) (hz p)) ▸ het
  obtain ⟨V, hv, _⟩ := bsem_exists_unique_l I hZF hc.wf N F x
  obtain ⟨v, _, h⟩ := nv_total_l I he hw hzT
  exact (bsat_root_l I hZF hpack hc hv hz).mpr
    ((nb_agree_l I hZF hω hA hc he hx hw hn hv z hzT v h).mpr (fun e => hn (Or.inl (e ▸ h))))

end YesMetaZFC.SetTheory.Descriptive
