import YesMetaZFC.Model.Forcing.Proper.Elementary.Membership
import YesMetaZFC.SetTheory.CountableCofinal

/-! # 内部可数初等模型的序数迹

若 β 是 N 中的极限序数，内部初等性保证 N∩β 无最大元。其真实交集与并确定
γ=sup(N∩β)，ZF 的最小上界构造给出取值于 N∩β 的内部 ω 共尾序列。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 只需传递环境中的内部初等性；无正则基数、反射或外部可数性假设。 -/
theorem selem_cofinal_sequence_l (hZF : M.Models ZF) {ω H c T d N S β α}
    (hω : M.IsOmega ω) (hH : M.TransitiveSet H)
    (hT : ∀ x y, M.PairMember I x y T ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d I c d H T N S) (hElem : Selem_d I ω c d)
    (hN : M.CardinalLessOrEqual I N ω) (hβ : M.IsLimitOrdinal β) (hβN : M.mem β N)
    (hαβ : M.mem α β) (hαN : M.mem α N) :
    ∃ A γ F, (∀ x, M.mem x A ↔ M.mem x N ∧ M.mem x β) ∧
      M.IsCofinalSubset A γ ∧ M.MemberSubset γ β ∧ M.IsSetFunctionFromTo I F ω A ∧
      M.IsCofinalNondecreasingOrdinalSequence I F ω γ ∧
      ∀ i x, M.PairMember I i x F → M.mem α x := by
  let L := smdl_structure_l I (R := T) hSub.source.2.1
  let Q := smdl_structure_l I (R := S) hSub.target.2.1
  have next x (hxN : M.mem x N) (hxβ : M.mem x β) : ∃ y, M.mem y N ∧ M.mem y β ∧ M.mem x y := by
    let ρ : Env L 2 := (⟨fun _ => ⟨β, hSub.subset β hβN⟩,
      fun _ => ⟨β, hSub.subset β hβN⟩⟩ : Env L 1).push ⟨x, hSub.subset x hxN⟩
    let η : Env Q 2 := (⟨fun _ => ⟨β, hβN⟩, fun _ => ⟨β, hβN⟩⟩ : Env Q 1).push ⟨x, hxN⟩
    let φ : UnarySchema 2 := { body := .conj (.mem .newest (.bound 2)) (.mem (.bound 1) .newest) }
    have hφ (y : L.Domain) : φ.denote ρ y ↔ M.mem y.val β ∧ M.mem x y.val := by
      simp only [φ, UnarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff]
      exact and_congr (smem_member_l I hSub.source hT y _) (smem_member_l I hSub.source hT _ y)
    obtain ⟨y, hy, hxy⟩ := hβ.2.2 x hxβ
    obtain ⟨z, hz⟩ := selem_witness_l I hZF hω hSub hElem φ ρ η (Fin.cases rfl (fun _ => rfl))
      ⟨⟨y, hH β (hSub.subset β hβN) y hy⟩, (hφ _).mpr ⟨hy, hxy⟩⟩
    exact ⟨z.val, z.property, (hφ _).mp hz⟩
  obtain ⟨A, hA⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) N β
  obtain ⟨f, hf⟩ := ZF.exists_inclusionInjection hZF I (fun x hx => ((hA x).mp hx).1)
  obtain ⟨g, hg⟩ := hN
  obtain ⟨γ, F, hγ, hγβ, hF, hc, hα⟩ := ZF.cc_cofinal_sequence_l I hZF hω hβ.1
    (fun x hx => ((hA x).mp hx).2) (ZF.exists_compositionInjection hZF I hf hg)
    ((hA α).mpr ⟨hαN, hαβ⟩) (fun x hx => by
      obtain ⟨y, hyN, hyβ, hxy⟩ := next x ((hA x).mp hx).1 ((hA x).mp hx).2
      exact ⟨y, (hA y).mpr ⟨hyN, hyβ⟩, hxy⟩)
  exact ⟨A, γ, F, hA, hγ, hγβ, hF, hc, hα⟩

end YesMetaZFC.Model.Forcing.Internal
