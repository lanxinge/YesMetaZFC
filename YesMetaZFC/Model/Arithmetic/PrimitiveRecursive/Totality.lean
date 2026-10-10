import YesMetaZFC.Model.Arithmetic.PrimitiveRecursive.Relation

/-! # 每个给定原始递归程序在 PA 模型中的总性与唯一性

外层只对宿主有限程序语法归纳；递归指令的内部步数由已验证的历史公式归纳处理。
这不是模型内部所有程序码的统一全称断言。
-/
namespace YesMetaZFC.Model.Arithmetic.PrimitiveRecursive
open Logic FirstOrder Logic.Arithmetic Logic.Arithmetic.PrimitiveRecursive
set_option autoImplicit false
universe u
variable {ℳ : Structure.{0, 0, 0, u} signature_m}
variable (hPA : Theory.Models ℳ Logic.Arithmetic.PA.theory_m)
include hPA

theorem exists_unique_m (c : code_m) (x : num_l ℳ) :
    ∃ y, relation_l c x y ∧ ∀ z, relation_l c x z → z = y := by
  induction c generalizing x with
  | zero => exact ⟨zero_l ℳ, rfl, fun _ h => h.symm⟩
  | succ => exact ⟨succ_l x, rfl, fun _ h => h.symm⟩
  | left =>
      obtain ⟨a, b, h⟩ := PA.Pairing.surjective_m hPA x
      refine ⟨a, ⟨b, h⟩, ?_⟩
      rintro z ⟨w, hw⟩
      exact (PA.Pairing.injective_m hPA z w a b hw h).1
  | right =>
      obtain ⟨a, b, h⟩ := PA.Pairing.surjective_m hPA x
      refine ⟨b, ⟨a, h⟩, ?_⟩
      rintro z ⟨w, hw⟩
      exact (PA.Pairing.injective_m hPA w z a b hw h).2
  | pair c d hc hd =>
      obtain ⟨a, ha, hca⟩ := hc x
      obtain ⟨b, hb, hdb⟩ := hd x
      obtain ⟨p, hp⟩ := Pairing.total_m a b
      refine ⟨p, ⟨a, b, ha, hb, hp⟩, ?_⟩
      rintro z ⟨v, w, hv, hw, hz⟩
      obtain rfl := hca v hv
      obtain rfl := hdb w hw
      exact Pairing.unique_m hz hp
  | comp c d hc hd =>
      obtain ⟨a, ha, hda⟩ := hd x
      obtain ⟨b, hb, hcb⟩ := hc a
      refine ⟨b, ⟨a, ha, hb⟩, ?_⟩
      rintro z ⟨v, hv, hz⟩
      exact hcb z (hda v hv ▸ hz)
  | prec c d hc hd =>
      let R := relation_l (ℳ := ℳ) c
      let S := iteration_l (relation_l (ℳ := ℳ) d)
      have hR (a : num_l ℳ) : ∃ v, R a v := let ⟨v, h, _⟩ := hc a; ⟨v, h⟩
      have hS (a i v : num_l ℳ) : ∃ w, S a i v w := by
        obtain ⟨p, hp⟩ := Pairing.total_m i v
        obtain ⟨q, hq⟩ := Pairing.total_m a p
        obtain ⟨w, hw, _⟩ := hd q
        exact ⟨w, p, q, hp, hq, hw⟩
      have hRu (a v w : num_l ℳ) (hv : R a v) (hw : R a w) : v = w := by
        obtain ⟨z, _, hz⟩ := hc a
        exact (hz v hv).trans (hz w hw).symm
      have hSu (a i v w z : num_l ℳ) (hw : S a i v w) (hz : S a i v z) : w = z := by
        obtain ⟨p, q, hp, hq, hw⟩ := hw
        obtain ⟨r, s, hr, hs, hz⟩ := hz
        obtain rfl := Pairing.unique_m hp hr
        obtain rfl := Pairing.unique_m hq hs
        obtain ⟨t, _, ht⟩ := hd q
        exact (ht w hw).trans (ht z hz).symm
      obtain ⟨a, n, hx⟩ := PA.Pairing.surjective_m hPA x
      obtain ⟨y, hy⟩ := PA.History.total_m (graph_m c) (iteration_m (graph_m d)) R S
        (graph_sat_m c) (iteration_sat_m (graph_m d) (relation_l d) (graph_sat_m d)) hPA hR hS a n
      refine ⟨y, ⟨a, n, hx, hy⟩, ?_⟩
      rintro z ⟨v, j, hpair, hz⟩
      obtain ⟨rfl, rfl⟩ := PA.Pairing.injective_m hPA v j a n hpair hx
      exact PA.History.unique_m hPA hRu hSu hz hy

theorem total_m (c : code_m) (x : num_l ℳ) : ∃ y, relation_l c x y := by
  obtain ⟨y, h, _⟩ := exists_unique_m hPA c x
  exact ⟨y, h⟩

theorem unique_m (c : code_m) {x y z : num_l ℳ} (hy : relation_l c x y) (hz : relation_l c x z) : y = z := by
  obtain ⟨a, _, h⟩ := exists_unique_m hPA c x
  exact (h y hy).trans (h z hz).symm

end YesMetaZFC.Model.Arithmetic.PrimitiveRecursive
