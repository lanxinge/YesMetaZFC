import YesMetaZFC.Model.Forcing.Iteration.Names.DenseProjection
import YesMetaZFC.Model.Forcing.Iteration.Names.Quotient

/-! # 同一内部模型中的稠密前缀见证

先把上层稠密集投影到前段，不相容分支补成全局稠密集。前段主条件在 N
中遇到此集合；初等性再把上层见证取回 N，拼接排除不相容分支。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

/-- 任意实际阶段链接把上层稠密集投影为前段的真实稠密集。 -/
theorem row_prj_dense_l {α B R e D V E r Z} (h : Row_stage_d M α B R e)
    (L : Cond_order_d M D V D) (k : Row_link_d I α B R D V)
    (hE : Dense_set_d M D V D E) (hr : M.mem r D) (hZ : Prj_set_d M B R D V E r Z) :
    Dense_set_d M B R B Z := by
  have self a (ha : M.mem a B) : M.IsRestrictionOf I a a α :=
    ⟨(h.rows a ha).graph, fun i s => ⟨fun hs => ⟨(h.rows a ha).domain i s hs, hs⟩, And.right⟩⟩
  refine ⟨fun a ha => ⟨hZ.1 a ha, ((hZ.2 a (hZ.1 a ha)).mp ha).1⟩, fun p hp hpz => ?_⟩
  classical
  by_cases hc : Cmp_d M D V D p r
  · obtain ⟨v, hvp, hvr⟩ := hc
    obtain ⟨s, hsv, hsE⟩ := hE.2 v hvp.1 hvp.2.1
    obtain ⟨a, ha, has⟩ := k.restrict s hsv.1
    have hsp := L.trans s v p hsv.1 hvp.1 (k.mem p hp) hsv.2.2 hvp.2.2
    have hap := k.mono s p a p hsv.1 (k.mem p hp) has (self p hp) hsp
    have haz : a ≠ B := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ ha)
    refine ⟨a, ⟨ha, haz, hap⟩, (hZ.2 a ha).mpr ⟨haz, Or.inr ⟨s, hsv.1, hsE,
      L.trans s v r hsv.1 hvp.1 hr hsv.2.2 hvr, ?_⟩⟩⟩
    intro b hb hsb
    exact k.mono s b a b hsv.1 (k.mem b hb) has (self b hb) hsb
  · exact ⟨p, below_refl_l h.order hp hpz, (hZ.2 p hp).mpr ⟨hpz, Or.inl hc⟩⟩

/-- 决定分支上的任意旧条件，都能在同一个 N 中加强进入指定稠密集。 -/
theorem row_dense_prefix_l {ω χ H c J d N S α B R e D V E r a p q}
    (hω : M.IsOmega ω) (hχ : M.IsLimitOrdinal χ) (hH : H_d I χ H)
    (hJ : ∀ x y, M.PairMember I x y J ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d I c d H J N S) (hElem : Selem_d I ω c d)
    (hB : M.mem B N) (hR : M.mem R N) (hD : M.mem D N) (hV : M.mem V N)
    (hE : M.mem E N) (hrN : M.mem r N) (h : Row_stage_d M α B R e)
    (L : Cond_order_d M D V D) (k : Row_link_d I α B R D V)
    (hd : Dense_set_d M D V D E) (hr : M.mem r D) (ha : M.mem a B) (har : M.IsRestrictionOf I a r α)
    (hm : Mstr_d M B R B N p) (hqp : Below_d M B R B q p) (hqa : Entry_d M q a R) :
    ∃ b s v, Below_d M B R B b q ∧ M.mem s N ∧ M.mem s D ∧ M.mem s E ∧ Entry_d M s r V ∧
      M.mem v B ∧ M.IsRestrictionOf I v s α ∧ Entry_d M b v R := by
  obtain ⟨⟨Z, hZN, hZ⟩, chooseN⟩ := selem_prj_set_l hZF hω hχ hH hJ hSub hElem hB hR hD hV hE hrN
  have hdZ := row_prj_dense_l hZF h L k hd hr hZ
  obtain ⟨u, huZ, huN, b, hbq, hbu⟩ := hm.2.2 Z hZN hdZ q hqp
  have huB := hZ.1 u huZ
  rcases ((hZ.2 u huB).mp huZ).2 with hn | hw
  · have hba := h.order.trans b q a hbq.1 hqp.1 ha hbq.2.2 hqa
    obtain ⟨w, hw⟩ := row_splice_exists_l M hZF α b r
    obtain ⟨hwD, hwr, hwb⟩ := k.splice r a b w hr har hbq.1 hba hw
    have hwu := L.trans w b u hwD (k.mem b hbq.1) (k.mem u huB) hwb ((k.order b u hbq.1 huB).mpr hbu)
    exact False.elim (hn ⟨w, ⟨hwD, (fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) D (he ▸ hwD)), hwu⟩, hwr⟩)
  · obtain ⟨s, hsN, hsD, hsE, hsr, hub⟩ := chooseN u huN hw
    obtain ⟨v, hv, hvs⟩ := k.restrict s hsD
    exact ⟨b, s, v, hbq, hsN, hsD, hsE, hsr, hv, hvs,
      h.order.trans b u v hbq.1 huB hv hbu (hub v hv (k.below s v hsD hvs))⟩

end YesMetaZFC.Model.Forcing.Internal
