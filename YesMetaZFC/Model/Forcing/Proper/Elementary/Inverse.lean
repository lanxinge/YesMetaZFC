import YesMetaZFC.Model.Forcing.Proper.Elementary.Countable
import YesMetaZFC.Model.Forcing.Internal.Reflection.Transitive

/-! # H(χ) 内关系图反向与初等闭包

反向图的原始成员受传递闭包的平方所界，故它是 H(χ) 中的实际集合。
其完整条目方程在传递隶属结构中绝对，初等性于是给出 N 内的同一反向图。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

/-- N 中实际有序对的两个坐标都在 N 中；只需传递环境中的内部初等性。 -/
theorem selem_kpair_coords_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
    {ω H c T d N S p a b} (hω : M.IsOmega ω) (hH : M.TransitiveSet H)
    (hT : ∀ x y, M.PairMember I x y T ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hS : Ssub_d I c d H T N S) (he : Selem_d I ω c d) (hp : M.mem p N)
    (hab : KPair_d M p a b) : M.mem a N ∧ M.mem b N := by
  let L := smdl_structure_l I (R := T) hS.source.2.1
  let Q := smdl_structure_l I (R := S) hS.target.2.1
  let ρ : Env L 1 := ⟨fun _ => ⟨p, hS.subset p hp⟩, fun _ => ⟨p, hS.subset p hp⟩⟩
  let η : Env Q 1 := ⟨fun _ => ⟨p, hp⟩, fun _ => ⟨p, hp⟩⟩
  let φ : BinarySchema 1 := { body := kpair_m (.bound 2) (.bound 1) .newest }
  have hφ (a b : L.Domain) : φ.denote ρ a b ↔ KPair_d M p a.val b.val :=
    (kpair_sat_l L (smem_ext_l I hS.source hT hH hZF.1) _ _ _ _).trans (smem_kpair_l I hS.source hT hH _ a b)
  have hc := trans_kpair_l hH (hS.subset p hp) hab
  obtain ⟨a', b', hab'⟩ := selem_binary_witness_l I hZF hω hS he φ ρ η (fun _ => rfl)
    ⟨⟨a, hc.1⟩, ⟨b, hc.2⟩, (hφ _ _).mpr hab⟩
  obtain ⟨ha, hb⟩ := kpair_injective_l M ((hφ _ _).mp hab') hab
  exact ⟨ha ▸ a'.property, hb ▸ b'.property⟩

def Inv_graph_d (M : SetTheory.Structure.{u}) (D F : M.Domain) : Prop :=
  (∀ v, M.mem v F → ∃ a b, KPair_d M v a b) ∧ ∀ a b, Entry_d M a b F ↔ Entry_d M b a D

def inv_graph_m {n} (D F : Term n) : Formula 1 n := .conj (Formula.isRelation kpair_convention_l F)
  (.forallE (.forallE (.iff (entry_m (.bound 1) .newest F.weaken.weaken)
    (entry_m .newest (.bound 1) D.weaken.weaken))))
derive_free_closed inv_graph_m

theorem inv_graph_sat_l (hE : Extensional M) {n} (ρ : Env M n) (D F : Term n) :
    Formula.satisfies ρ (inv_graph_m D F) ↔ Inv_graph_d M (D.eval ρ) (F.eval ρ) := by
  simp only [inv_graph_m, Inv_graph_d, Formula.isRelation, Formula.satisfies_conj_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff, kpair_convention_l,
    kpair_sat_l M hE, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, entry_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem smem_inv_graph_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
    {c H T} (hM : Smdl_d I c H T)
    (hT : ∀ x y, M.PairMember I x y T ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y) (hH : M.TransitiveSet H)
    (D F : (smdl_structure_l I (R := T) hM.2.1).Domain) :
    Inv_graph_d (smdl_structure_l I (R := T) hM.2.1) D F ↔ Inv_graph_d M D.val F.val := by
  let L := smdl_structure_l I (R := T) hM.2.1
  constructor
  · rintro ⟨hg, he⟩
    constructor
    · intro v hv
      let v' : L.Domain := ⟨v, hH F.val F.property v hv⟩
      obtain ⟨a, b, hab⟩ := hg v' ((smem_member_l I hM hT v' F).mpr hv)
      exact ⟨a.val, b.val, (smem_kpair_l I hM hT hH v' a b).mp hab⟩
    · intro a b
      constructor
      · intro hab
        let a' : L.Domain := ⟨a, (trans_entry_l hH F.property hab).1⟩
        let b' : L.Domain := ⟨b, (trans_entry_l hH F.property hab).2⟩
        exact (smem_entry_l I hM hT hH b' a' D).mp ((he a' b').mp ((smem_entry_l I hM hT hH a' b' F).mpr hab))
      · intro hba
        let a' : L.Domain := ⟨a, (trans_entry_l hH D.property hba).2⟩
        let b' : L.Domain := ⟨b, (trans_entry_l hH D.property hba).1⟩
        exact (smem_entry_l I hM hT hH a' b' F).mp ((he a' b').mpr ((smem_entry_l I hM hT hH b' a' D).mpr hba))
  · rintro ⟨hg, he⟩
    constructor
    · intro v hv
      obtain ⟨a, b, hab⟩ := hg v.val ((smem_member_l I hM hT v F).mp hv)
      exact ⟨⟨a, (trans_kpair_l hH v.property hab).1⟩, ⟨b, (trans_kpair_l hH v.property hab).2⟩,
        (smem_kpair_l I hM hT hH v _ _).mpr hab⟩
    · exact fun a b => (smem_entry_l I hM hT hH a b F).trans ((he a.val b.val).trans (smem_entry_l I hM hT hH b a D).symm)

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem h_inverse_l {ω χ H D} (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I χ)
    (hωχ : M.mem ω χ) (hH : H_d I χ H) (hD : M.mem D H) : ∃ F, M.mem F H ∧ Inv_graph_d M D F := by
  obtain ⟨T, μ, hT, hμ, hTc⟩ := (hH D).mp hD
  have hTH := (hH T).mpr (ZF.hmem_of_subset_l I hZF hχ.isLimitOrdinal hT.1 (fun _ h => h) hμ hTc)
  let ρ : Env M 1 := ⟨fun _ => D, fun _ => D⟩
  let φ : BinarySchema 1 := { body := entry_m .newest (.bound 1) (.bound 2) }
  obtain ⟨F, hF, hf⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ T
  have he a b : Entry_d M a b F ↔ Entry_d M b a D := by
    have h := (hf a b).trans (and_congr_right fun _ => and_congr_right fun _ => entry_sat_l M hZF.1 _ _ _ _)
    exact h.trans ⟨And.right ∘ And.right, fun h => ⟨(trans_entry_l hT.1 hT.2.1 h).2, (trans_entry_l hT.1 hT.2.1 h).1, h⟩⟩
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I T T
  have hFP : M.MemberSubset F P := by
    intro v hv
    obtain ⟨a, b, hab⟩ := hF.1 v hv
    have ht := hF.2 a b ⟨v, hab, hv⟩
    exact (hP v).mpr ⟨a, ht.1, b, ht.2, hab⟩
  exact ⟨F, ZF.h_subsets_l I hZF hχ.isLimitOrdinal hH (h_product_l hZFC hω hχ hωχ hH hTH hTH hP) F hFP, hF.1, he⟩

theorem selem_inverse_l {ω χ H c T d N S D} (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I χ)
    (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hT : ∀ x y, M.PairMember I x y T ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hS : Ssub_d I c d H T N S) (he : Selem_d I ω c d) (hD : M.mem D N) : ∃ F, M.mem F N ∧ Inv_graph_d M D F := by
  let L := smdl_structure_l I (R := T) hS.source.2.1
  let Q := smdl_structure_l I (R := S) hS.target.2.1
  have htr := ZF.h_transitive_l I hZF hH
  let ρ : Env L 1 := ⟨fun _ => ⟨D, hS.subset D hD⟩, fun _ => ⟨D, hS.subset D hD⟩⟩
  let η : Env Q 1 := ⟨fun _ => ⟨D, hD⟩, fun _ => ⟨D, hD⟩⟩
  let φ : UnarySchema 1 := { body := inv_graph_m (.bound 1) .newest }
  have hφ (F : L.Domain) : φ.denote ρ F ↔ Inv_graph_d M D F.val :=
    (inv_graph_sat_l (smem_ext_l I hS.source hT htr hZF.1) _ _ _).trans (smem_inv_graph_l I hS.source hT htr _ F)
  obtain ⟨F, hFH, hF⟩ := h_inverse_l hZFC hω hχ hωχ hH (hS.subset D hD)
  obtain ⟨F', hF'⟩ := selem_witness_l I hZF hω hS he φ ρ η (fun _ => rfl) ⟨⟨F, hFH⟩, (hφ _).mpr hF⟩
  exact ⟨F'.val, F'.property, (hφ _).mp hF'⟩

theorem selem_kpair_closed_l {ω χ H c T d N S p a b} (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I χ)
    (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hT : ∀ x y, M.PairMember I x y T ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hS : Ssub_d I c d H T N S) (he : Selem_d I ω c d) (ha : M.mem a N) (hb : M.mem b N)
    (hp : KPair_d M p a b) : M.mem p N := by
  let L := smdl_structure_l I (R := T) hS.source.2.1
  let Q := smdl_structure_l I (R := S) hS.target.2.1
  have htr := ZF.h_transitive_l I hZF hH
  let ρ : Env L 2 := (⟨fun _ => ⟨a, hS.subset a ha⟩, fun _ => ⟨a, hS.subset a ha⟩⟩ : Env L 1).push ⟨b, hS.subset b hb⟩
  let η : Env Q 2 := (⟨fun _ => ⟨a, ha⟩, fun _ => ⟨a, ha⟩⟩ : Env Q 1).push ⟨b, hb⟩
  let φ : UnarySchema 2 := { body := kpair_m .newest (.bound 2) (.bound 1) }
  have hφ (p : L.Domain) : φ.denote ρ p ↔ KPair_d M p.val a b :=
    (kpair_sat_l L (smem_ext_l I hS.source hT htr hZF.1) _ _ _ _).trans (smem_kpair_l I hS.source hT htr p _ _)
  have hpH := h_kpair_l hZFC hω hχ hωχ hH hp (hS.subset a ha) (hS.subset b hb)
  obtain ⟨p', hp'⟩ := selem_witness_l I hZF hω hS he φ ρ η (Fin.cases rfl (fun _ => rfl)) ⟨⟨p, hpH⟩, (hφ _).mpr hp⟩
  exact kpair_unique_l M hZF.1 ((hφ _).mp hp') hp ▸ p'.property

end YesMetaZFC.Model.Forcing.Internal
