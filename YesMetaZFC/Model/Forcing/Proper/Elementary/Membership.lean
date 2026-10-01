import YesMetaZFC.Model.SetTheory.Internal.SourceElementary
import YesMetaZFC.Model.SetTheory.Internal.Membership
import YesMetaZFC.Model.Forcing.Internal.Check.Syntax

/-! # 内部初等子模型中的实际关系见证

在传递集合的隶属结构中，有序对及其图条目绝对。先通过内部初等性反射存在
公式，再把见证公式传回大结构，因而不要求非传递子模型本身具有有序对绝对性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
variable {c X R : M.Domain} (hM : Smdl_d I c X R)
  (hR : ∀ x y, M.PairMember I x y R ↔ M.mem x X ∧ M.mem y X ∧ M.mem x y)
  (hX : M.TransitiveSet X)
local notation "L" => smdl_structure_l I (R := R) (And.left (And.right hM))
include hR

include hX in
theorem smem_pair_l (p a b : (L).Domain) : Pair_d L p a b ↔ Pair_d M p.val a.val b.val := by
  constructor
  · intro h x
    constructor
    · intro hx
      let y : (L).Domain := ⟨x, hX p.val p.property x hx⟩
      exact ((h y).mp ((smem_member_l I hM hR y p).mpr hx)).elim
        (fun he => Or.inl (congrArg Subtype.val he)) (fun he => Or.inr (congrArg Subtype.val he))
    · rintro (rfl | rfl)
      · exact (smem_member_l I hM hR a p).mp ((h a).mpr (Or.inl rfl))
      · exact (smem_member_l I hM hR b p).mp ((h b).mpr (Or.inr rfl))
  · intro h x
    exact (smem_member_l I hM hR x p).trans ((h x.val).trans
      (or_congr ⟨Subtype.ext, congrArg Subtype.val⟩ ⟨Subtype.ext, congrArg Subtype.val⟩))

include hX in
theorem smem_single_l (p a : (L).Domain) : (L).IsSingletonOf p a ↔ M.IsSingletonOf p.val a.val := by
  have conv {K : SetTheory.Structure} (p a : K.Domain) : K.IsSingletonOf p a ↔ Pair_d K p a a := by
    simp only [Structure.IsSingletonOf, Pair_d, or_self]
  exact (conv p a).trans ((smem_pair_l I hM hR hX p a a).trans (conv p.val a.val).symm)

include hX in
theorem smem_kpair_l (p a b : (L).Domain) : KPair_d L p a b ↔ KPair_d M p.val a.val b.val := by
  constructor
  · rintro ⟨s, t, hs, ht, hp⟩
    exact ⟨s.val, t.val, (smem_single_l I hM hR hX s a).mp hs,
      (smem_pair_l I hM hR hX t a b).mp ht, (smem_pair_l I hM hR hX p s t).mp hp⟩
  · rintro ⟨s, t, hs, ht, hp⟩
    let s' : (L).Domain := ⟨s, hX p.val p.property s ((hp s).mpr (Or.inl rfl))⟩
    let t' : (L).Domain := ⟨t, hX p.val p.property t ((hp t).mpr (Or.inr rfl))⟩
    exact ⟨s', t', (smem_single_l I hM hR hX s' a).mpr hs,
      (smem_pair_l I hM hR hX t' a b).mpr ht, (smem_pair_l I hM hR hX p s' t').mpr hp⟩

include hX in
theorem smem_entry_l (a b F : (L).Domain) : Entry_d L a b F ↔ Entry_d M a.val b.val F.val := by
  constructor
  · rintro ⟨p, hp, hpF⟩
    exact ⟨p.val, (smem_kpair_l I hM hR hX p a b).mp hp, (smem_member_l I hM hR p F).mp hpF⟩
  · rintro ⟨p, hp, hpF⟩
    let p' : (L).Domain := ⟨p, hX F.val F.property p hpF⟩
    exact ⟨p', (smem_kpair_l I hM hR hX p' a b).mpr hp, (smem_member_l I hM hR p' F).mpr hpF⟩

include hX in
omit hM in
/-- 只要实际关系图和第二坐标属于 N，任何存在的第一坐标见证都可取在 N 中。 -/
theorem selem_entry_witness_l (hZF : M.Models ZF) {ω d N S F p} (hω : M.IsOmega ω)
    (hS : Ssub_d I c d X R N S) (h : Selem_d I ω c d) (hF : M.mem F N) (hp : M.mem p N)
    (he : ∃ s, Entry_d M s p F) : ∃ s, M.mem s N ∧ Entry_d M s p F := by
  let A := smdl_structure_l I (R := R) hS.source.2.1
  let Q := smdl_structure_l I (R := S) hS.target.2.1
  let ρ : Env A 2 := (⟨fun _ => ⟨F, hS.subset F hF⟩, fun _ => ⟨F, hS.subset F hF⟩⟩ : Env A 1).push ⟨p, hS.subset p hp⟩
  let η : Env Q 2 := (⟨fun _ => ⟨F, hF⟩, fun _ => ⟨F, hF⟩⟩ : Env Q 1).push ⟨p, hp⟩
  let φ : UnarySchema 2 := { body := entry_m .newest (.bound 1) (.bound 2) }
  have hφ (s : A.Domain) : φ.denote ρ s ↔ Entry_d M s.val p F :=
    (entry_sat_l A (smem_ext_l I hS.source hR hX hZF.1) _ _ _ _).trans
      (smem_entry_l I hS.source hR hX s ⟨p, hS.subset p hp⟩ ⟨F, hS.subset F hF⟩)
  obtain ⟨s, hs⟩ := he
  have hsX : M.mem s X := by
    obtain ⟨r, hr, hrF⟩ := hs
    obtain ⟨t, htr, hst⟩ := (kpair_union_l M hr s).mpr (Or.inl rfl)
    exact hX t (hX r (hX F (hS.subset F hF) r hrF) t htr) s hst
  obtain ⟨t, ht⟩ := selem_witness_l I hZF hω hS h φ ρ η (Fin.cases rfl (fun _ => rfl))
    ⟨⟨s, hsX⟩, (hφ ⟨s, hsX⟩).mpr hs⟩
  exact ⟨t.val, t.property, (hφ ⟨t.val, hS.subset t.val t.property⟩).mp ht⟩

include hX in
omit hM in
/-- 内部初等模型对其中实际函数图的求值封闭，只使用图的单值性。 -/
theorem selem_entry_value_l (hZF : M.Models ZF) {ω d N S F p q} (hω : M.IsOmega ω)
    (hS : Ssub_d I c d X R N S) (h : Selem_d I ω c d) (hF : M.mem F N) (hp : M.mem p N)
    (hf : ∀ i s t, Entry_d M i s F → Entry_d M i t F → s = t) (hpq : Entry_d M p q F) : M.mem q N := by
  let A := smdl_structure_l I (R := R) hS.source.2.1
  let Q := smdl_structure_l I (R := S) hS.target.2.1
  let ρ : Env A 2 := (⟨fun _ => ⟨F, hS.subset F hF⟩, fun _ => ⟨F, hS.subset F hF⟩⟩ : Env A 1).push ⟨p, hS.subset p hp⟩
  let η : Env Q 2 := (⟨fun _ => ⟨F, hF⟩, fun _ => ⟨F, hF⟩⟩ : Env Q 1).push ⟨p, hp⟩
  let φ : UnarySchema 2 := { body := entry_m (.bound 1) .newest (.bound 2) }
  have hφ (s : A.Domain) : φ.denote ρ s ↔ Entry_d M p s.val F :=
    (entry_sat_l A (smem_ext_l I hS.source hR hX hZF.1) _ _ _ _).trans
      (smem_entry_l I hS.source hR hX ⟨p, hS.subset p hp⟩ s ⟨F, hS.subset F hF⟩)
  have hqX : M.mem q X := by
    obtain ⟨r, hr, hrF⟩ := hpq
    obtain ⟨t, htr, hqt⟩ := (kpair_union_l M hr q).mpr (Or.inr rfl)
    exact hX t (hX r (hX F (hS.subset F hF) r hrF) t htr) q hqt
  obtain ⟨s, hs⟩ := selem_witness_l I hZF hω hS h φ ρ η (Fin.cases rfl (fun _ => rfl))
    ⟨⟨q, hqX⟩, (hφ _).mpr hpq⟩
  exact (hf p s.val q ((hφ _).mp hs) hpq) ▸ s.property

end YesMetaZFC.Model.Forcing.Internal
