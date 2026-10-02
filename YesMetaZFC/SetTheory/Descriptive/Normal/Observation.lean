import YesMetaZFC.SetTheory.Descriptive.Normal.Complete

/-! # 有限观察的合并

观察用一对相同内部长度的前缀给出，并在任何图延拓上保持成立。
合取取较长前缀；本层仅作证明组织，最终证书仍由原公式定义。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def No_d (ω x w : M.Domain) (P : M.Domain → M.Domain → Prop) : Prop := ∃ n s t,
  M.mem n ω ∧ M.IsRestrictionOf I s x n ∧ M.IsRestrictionOf I t w n ∧
    ∀ u v, M.MemberSubset s u → M.MemberSubset t v → P u v

theorem no_map_l {ω x w} {P Q : M.Domain → M.Domain → Prop} (h : No_d I ω x w P)
    (f : ∀ u v, P u v → Q u v) : No_d I ω x w Q := by
  obtain ⟨n, s, t, hn, hs, ht, h⟩ := h
  exact ⟨n, s, t, hn, hs, ht, fun u v hu hv => f u v (h u v hu hv)⟩

theorem no_and_l (hZF : M.Models ZF) {ω x w} (hω : M.IsOmega ω)
    (hx : M.IsSetFunctionFromTo I x ω ω) (hw : M.IsSetFunctionFromTo I w ω ω)
    {P Q : M.Domain → M.Domain → Prop} (h : No_d I ω x w P) (k : No_d I ω x w Q) :
    No_d I ω x w (fun u v => P u v ∧ Q u v) := by
  obtain ⟨n, s, t, hn, hs, ht, h⟩ := h
  obtain ⟨m, u, v, hm, hu, hv, k⟩ := k
  have inc {f n m s t} (hf : M.IsSetFunctionFromTo I f ω ω) (hn : M.mem n ω) (hm : M.mem m ω)
      (hs : M.IsRestrictionOf I s f n) (ht : M.IsRestrictionOf I t f m) (h : M.MemberSubset n m) :=
    ds_prefix_mono_l I (hs.isSetFunctionFromTo hf (hω.transitive hZF n hn))
      (ht.isSetFunctionFromTo hf (hω.transitive hZF m hm)).1 hs ht h
  have le : M.MemberSubset n m ∨ M.MemberSubset m n := by
    rcases (hω.isOrdinal hZF).wellOrder.linear.compare n hn m hm with e | h | h
    · exact Or.inl (fun a => (e a).mp)
    · exact Or.inl (((hω.isOrdinal hZF).mem hm).transitive n h)
    · exact Or.inr (((hω.isOrdinal hZF).mem hn).transitive m h)
  rcases le with le | le
  · exact ⟨m, u, v, hm, hu, hv, fun a b ha hb =>
      ⟨h a b (fun p hp => ha p (inc hx hn hm hs hu le p hp)) (fun p hp => hb p (inc hw hn hm ht hv le p hp)), k a b ha hb⟩⟩
  · exact ⟨n, s, t, hn, hs, ht, fun a b ha hb =>
      ⟨h a b ha hb, k a b (fun p hp => ha p (inc hx hm hn hu hs le p hp)) (fun p hp => hb p (inc hw hm hn hv ht le p hp))⟩⟩

theorem no_pair_l (hZF : M.Models ZF) {ω x w i a} (hω : M.IsOmega ω)
    (hx : M.IsSetFunctionFromTo I x ω ω) (hw : M.IsSetFunctionFromTo I w ω ω)
    (b : Bool) (h : M.PairMember I i a (if b then w else x)) :
    No_d I ω x w (fun u v => M.PairMember I i a (if b then v else u)) := by
  have hi : M.mem i ω := by cases b; exact hx.input_mem_of_pairMember h; exact hw.input_mem_of_pairMember h
  obtain ⟨n, hn, hnω⟩ := hω.1.2 i hi
  obtain ⟨s, _, hs, _⟩ := ds_prefix_l I hZF hω hx hnω
  obtain ⟨t, _, ht, _⟩ := ds_prefix_l I hZF hω hw hnω
  refine ⟨n, s, t, hnω, hs, ht, fun u v hu hv => ?_⟩
  cases b
  · exact ((hs.2 i a).mpr ⟨hn.predecessor_mem, h⟩).elim fun p hp => ⟨p, hp.1, hu p hp.2⟩
  · exact ((ht.2 i a).mpr ⟨hn.predecessor_mem, h⟩).elim fun p hp => ⟨p, hp.1, hv p hp.2⟩

theorem no_nv_l (hZF : M.Models ZF) {ω E x w a v} (hω : M.IsOmega ω)
    (hx : M.IsSetFunctionFromTo I x ω ω) (hw : M.IsSetFunctionFromTo I w ω ω) (h : Nv_d I E w a v) :
    No_d I ω x w (fun _ t => Nv_d I E t a v) := by
  obtain ⟨i, hi, hv⟩ := h
  exact no_map_l I (no_pair_l I hZF hω hx hw true hv) (fun _ _ h => ⟨i, hi, h⟩)

theorem no_sub_l (hZF : M.Models ZF) {ω A x w s} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hx : M.IsSetFunctionFromTo I x ω ω)
    (hw : M.IsSetFunctionFromTo I w ω ω) (hs : M.mem s A) (h : M.MemberSubset s x) :
    No_d I ω x w (fun u _ => M.MemberSubset s u) := by
  obtain ⟨n, hn, hs⟩ := (hA s).mp hs
  obtain ⟨t, _, ht, _⟩ := ds_prefix_l I hZF hω hw hn
  exact ⟨n, s, t, hn, (ds_restrict_iff_l I hs hx.1).mpr h, ht, fun _ _ h _ => h⟩

theorem nb_observe_l (hZF : M.Models ZF) {ω A T R N F E z x w} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hc : Btree_d I ω A A T R N F)
    (hx : M.IsSetFunctionFromTo I x ω ω) (hw : M.IsSetFunctionFromTo I w ω ω)
    (h : Nb_d I T R N F E z x w) : No_d I ω x w (fun u v => Nb_d I T R N F E z u v) := by
  have read {a v} (h : Nv_d I E w a v) := no_nv_l I hZF hω hx hw h
  rcases h with h | h | h | ⟨a, v, hu, hav, h⟩
  · exact no_map_l I (read h) (fun _ _ h => Or.inl h)
  · obtain ⟨a, s, v, hs, hav, hsx | ⟨hne, j, b, c, hjs, hjx, hbc⟩⟩ := h
    · exact no_map_l I (no_and_l I hZF hω hx hw (read hav)
        (no_sub_l I hZF hω hA hx hw (hc.leaf a s hs).2.1 hsx.2))
        (fun _ _ h => Or.inr (Or.inl ⟨a, s, v, hs, h.1, Or.inl ⟨hsx.1, h.2⟩⟩))
    · exact no_map_l I (no_and_l I hZF hω hx hw (read hav) (no_pair_l I hZF hω hx hw false hjx))
        (fun _ _ h => Or.inr (Or.inl ⟨a, s, v, hs, h.1, Or.inr ⟨hne, j, b, c, hjs, h.2, hbc⟩⟩))
  · obtain ⟨a, b, v, u, haN, hba, hav, hbu, eqn⟩ := h
    exact no_map_l I (no_and_l I hZF hω hx hw (read hav) (read hbu))
      (fun _ _ h => Or.inr (Or.inr (Or.inl ⟨a, b, v, u, haN, hba, h.1, h.2, eqn⟩)))
  · rcases h with ⟨e, b, u, hb, hba, hbu, hne⟩ | ⟨hne, hn⟩ | ⟨b, j, hb, hba, hbj, hj, hbz⟩
    · exact no_map_l I (no_and_l I hZF hω hx hw (read hav) (read hbu))
        (fun _ _ h => Or.inr (Or.inr (Or.inr ⟨a, v, hu, h.1, Or.inl ⟨e, b, u, hb, hba, h.2, hne⟩⟩)))
    · exact no_map_l I (read hav)
        (fun _ _ h => Or.inr (Or.inr (Or.inr ⟨a, v, hu, h, Or.inr (Or.inl ⟨hne, hn⟩)⟩)))
    · exact no_map_l I (no_and_l I hZF hω hx hw (read hav) (read hbz))
        (fun _ _ h => Or.inr (Or.inr (Or.inr ⟨a, v, hu, h.1, Or.inr (Or.inr ⟨b, j, hb, hba, hbj, hj, h.2⟩)⟩)))

end YesMetaZFC.SetTheory.Descriptive
