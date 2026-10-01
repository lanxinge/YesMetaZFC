import YesMetaZFC.Model.Forcing.Iteration.Condition.Projection
import YesMetaZFC.Model.Forcing.Stage.Embedding

/-! # 由坐标限制投影构造实际完全嵌入

嵌入图就是旧条件集上的恒等图。限制投影反射共同加强，前缀拼接产生约减
所需的共同加强，因此可直接接入既有名称搬运与泛型回拉设施。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

theorem row_link_embed_l (hZF : M.Models ZF) {α B R D V}
    (h : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R D V) : ∃ G,
      (∀ p q, Entry_d M p q G ↔ M.mem p B ∧ q = p) ∧ Reg_embed_d M B R B D V D G := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => B⟩
  let φ : BinarySchema 0 := { body := Formula.extensionalEq .newest (.bound 1) }
  have hφ p q : φ.denote ρ p q ↔ q = p := Formula.satisfies_extensionalEq_iff_eq hZF.1 _ _ _
  obtain ⟨G, hGraph, hG'⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ B
  have hG p q : Entry_d M p q G ↔ M.mem p B ∧ q = p := by
    refine (hG' p q).trans ?_
    rw [hφ p q]
    exact ⟨fun hh => ⟨hh.1, hh.2.2⟩, fun ⟨hp, he⟩ => ⟨hp, he.symm ▸ hp, he⟩⟩
  have nz {X p} (hp : M.mem p X) : p ≠ X := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) X (he ▸ hp)
  have self p (hp : M.mem p B) : M.IsRestrictionOf I p p α :=
    ⟨(h.rows p hp).graph, fun i s => ⟨fun his => ⟨(h.rows p hp).domain i s his, his⟩, And.right⟩⟩
  refine ⟨G, hG, {
    graph := hGraph.1
    total := fun p hp _ => ⟨p, (hG p p).mpr ⟨hp, rfl⟩⟩
    domain := ?_, functional := ?_, injective := ?_, order := ?_, compat := ?_, reduction := ?_ }⟩
  · intro p q hpq
    obtain ⟨hp, he⟩ := (hG p q).mp hpq
    subst q
    exact ⟨hp, nz hp, h.mem p hp, nz (h.mem p hp)⟩
  · intro p q r hpq hpr
    exact ((hG p q).mp hpq).2.trans ((hG p r).mp hpr).2.symm
  · intro p q r hpr hqr
    exact ((hG p r).mp hpr).2.symm.trans ((hG q r).mp hqr).2
  · intro p q x y hpx hqy
    obtain ⟨hp, hx⟩ := (hG p x).mp hpx
    obtain ⟨hq, hy⟩ := (hG q y).mp hqy
    subst x
    subst y
    exact h.order p q hp hq
  · intro p q x y hpx hqy
    obtain ⟨hp, hx⟩ := (hG p x).mp hpx
    obtain ⟨hq, hy⟩ := (hG q y).mp hqy
    subst x
    subst y
    constructor
    · rintro ⟨r, hrp, hrq⟩
      obtain ⟨a, ha, har⟩ := h.restrict r hrp.1
      exact ⟨a, ⟨ha, nz ha, h.mono r p a p hrp.1 (h.mem p hp) har (self p hp) hrp.2.2⟩,
        h.mono r q a q hrp.1 (h.mem q hq) har (self q hq) hrq⟩
    · rintro ⟨r, hrp, hrq⟩
      exact ⟨r, ⟨h.mem r hrp.1, nz (h.mem r hrp.1), (h.order r p hrp.1 hp).mpr hrp.2.2⟩,
        (h.order r q hrp.1 hq).mpr hrq⟩
  · intro p hp _
    obtain ⟨a, ha, hap⟩ := h.restrict p hp
    refine ⟨a, ha, nz ha, fun q y hqy hqa => ?_⟩
    obtain ⟨hq, hy⟩ := (hG q y).mp hqy
    subst y
    obtain ⟨r, hr⟩ := row_splice_exists_l M hZF α q p
    obtain ⟨hrD, hrp, hrq⟩ := h.splice p a q r hp hap hq hqa hr
    exact ⟨r, ⟨hrD, nz hrD, hrp⟩, hrq⟩

end YesMetaZFC.Model.Forcing.Internal
