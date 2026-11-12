import YesMetaZFC.SetTheory.Collapse.NaturalBasis

/-! # 实际函数图的成员支撑及二值实数固定

源坐标已固定时，任何合法有序对的像都保持第一坐标。由函数单值性，
一个已固定的函数图的每个有序对成员也被固定。常零、后继图由此提供
全部二值图所需的支撑；二值取值为零或该输入的后继，毋须另添恒等实数。
-/
namespace YesMetaZFC.SetTheory
open InnerModel
universe u
variable {M : Structure.{u}} {Q B F : M.Domain} (h : Mc_map_d Q B F) (ht : M.TransitiveSet B)

namespace Mc_map_d
include h ht

/-- 只要原第一坐标有像，合法有序对的第一坐标就不会漂移。 -/
theorem kpair_first_l {p q a b x y u : M.Domain} (hp : KPair_d M p a b)
    (hq : KPair_d M q x y) (edge : Rd_entry_d p q F) (ea : Rd_entry_d a u F) : u = x := by
  obtain ⟨s,t,single,pair,outer⟩ := hp
  obtain ⟨v,_,single',_,outer'⟩ := hq
  have vq := (outer' v).mpr (Or.inl rfl)
  obtain ⟨r,er⟩ := h.onto v (ht q (h.function.bound_l edge).2 v vq)
  have rp := (h.member r p v q er edge).mpr vq
  have ar : M.mem a r := ((outer r).mp rp).elim
    (fun eq => eq.symm ▸ (single a).mpr rfl) (fun eq => eq.symm ▸ (pair a).mpr (Or.inl rfl))
  exact (single' u).mp ((h.member a r u v ea er).mp ar)

/-- 固定定义域和图本身，便逐点固定图的全部 Kuratowski 成员。 -/
theorem function_support_l (hE : Extensional M) {D V r : M.Domain} (fr : Fn0_d D V r)
    (er : Rd_entry_d r r F) (fixed : ∀ a, M.mem a D → Rd_entry_d a a F) :
    ∀ p, M.mem p r → Rd_entry_d p p F := by
  intro p hp
  obtain ⟨a,ha,b,hb,pair⟩ := fr.1 p hp
  obtain ⟨q,eq⟩ := h.onto p (ht r (h.function.bound_l er).2 p hp)
  have hq := (h.member q r p r eq er).mpr hp
  obtain ⟨x,hx,y,hy,pair'⟩ := fr.1 q hq
  have xa := h.kpair_first_l ht pair' pair eq (fixed x hx)
  subst x
  have yb := fr.2.2 a ha y hy b hb ⟨q,pair',hq⟩ ⟨p,pair,hp⟩
  subst y
  exact kpair_unique_l M hE pair' pair ▸ eq

/-- 所有原成员逐点固定时，整个集合的实际像也固定。 -/
theorem fixed_of_members_l (hE : Extensional M) {a b : M.Domain} (edge : Rd_entry_d a b F)
    (fixed : ∀ x, M.mem x a → Rd_entry_d x x F) : a = b := by
  apply hE.eq_of_same_members
  intro x
  constructor
  · intro hx
    exact (h.member x a x b (fixed x hx) edge).mp hx
  · intro hx
    obtain ⟨y,ey⟩ := h.onto x (ht b (h.function.bound_l edge).2 x hx)
    have hy := (h.member y a x b ey edge).mpr hx
    have eq := h.function.2.2 y (h.function.bound_l ey).1 x (h.function.bound_l ey).2
      y (h.function.bound_l (fixed y hy)).2 ey (fixed y hy)
    exact eq.symm ▸ hy

/-- 常零与后继的两套成员支撑覆盖全部二值图，不要求源对幂集或分离封闭。 -/
theorem binary_fixed_l (hE : Extensional M) {ω z c s r v : M.Domain} (basis : Mc_nat_d ω z c s)
    (ec : Rd_entry_d c c F) (es : Rd_entry_d s s F)
    (fixed : ∀ n, M.mem n ω → Rd_entry_d n n F)
    (fr : Fn0_d ω ω r) (bits : ∀ n y, Rd_entry_d n y r → y = z ∨ M.SuccessorOf y n)
    (er : Rd_entry_d r v F) : r = v := by
  have cs := h.function_support_l ht hE basis.constant ec fixed
  have ss := h.function_support_l ht hE basis.successor es fixed
  apply h.fixed_of_members_l ht hE er
  intro p hp
  obtain ⟨n,hn,y,_,pair⟩ := fr.1 p hp
  have in_graph {f : M.Domain} (edge : Rd_entry_d n y f) : M.mem p f := by
    obtain ⟨q,qp,hq⟩ := edge
    exact kpair_unique_l M hE qp pair ▸ hq
  rcases bits n y ⟨p,pair,hp⟩ with eq | succ
  · exact cs p (in_graph ((basis.constant_entry n y).mpr ⟨hn,eq⟩))
  · exact ss p (in_graph ((basis.successor_entry n y).mpr ⟨hn,succ⟩))

end Mc_map_d
end YesMetaZFC.SetTheory
