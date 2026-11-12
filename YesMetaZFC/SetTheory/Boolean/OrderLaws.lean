import YesMetaZFC.SetTheory.Boolean.Algebra

/-! # 集合编码布尔代数的相交与补元判别

所有运算仍使用已有的存在唯一图关系，不选择宿主层的运算函数。
核的单射性归结为 a≤b 当且仅当 a∧¬b=0。
-/
namespace YesMetaZFC.SetTheory.BooleanZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
variable {B R z : M.Domain}

theorem Meet_d.unique_l {a b c d : M.Domain} (order : Order_d I B R)
    (h : Meet_d I B R a b c) (k : Meet_d I B R a b d) : c = d :=
  order.antisymm c d h.1 k.1 ((k.2 c h.1).mpr (meet_bounds_d I order h))
    ((h.2 d k.1).mpr (meet_bounds_d I order k))

theorem Imp_d.unique_l {a b c d : M.Domain} (order : Order_d I B R)
    (h : Imp_d I B R a b c) (k : Imp_d I B R a b d) : c = d := by
  have hc := (h.2 c h.1).mp (order.refl c h.1)
  have hd := (k.2 d k.1).mp (order.refl d k.1)
  exact order.antisymm c d h.1 k.1 ((k.2 c h.1).mpr hc) ((h.2 d k.1).mpr hd)

theorem meet_of_le_l {a b : M.Domain} (order : Order_d I B R)
    (ha : M.mem a B) (hb : M.mem b B) (ab : M.PairMember I a b R) : Meet_d I B R a b a :=
  ⟨ha,fun d hd => ⟨fun da => ⟨da,order.trans d a b hd ha hb da ab⟩,And.left⟩⟩

theorem Meet_d.mono_l {a b c a' b' c' : M.Domain} (order : Order_d I B R)
    (ha : M.mem a B) (hb : M.mem b B) (ha' : M.mem a' B) (hb' : M.mem b' B)
    (h : Meet_d I B R a b c) (k : Meet_d I B R a' b' c')
    (aa : M.PairMember I a a' R) (bb : M.PairMember I b b' R) : M.PairMember I c c' R :=
  (k.2 c h.1).mpr ⟨order.trans c a a' h.1 ha ha' (meet_bounds_d I order h).1 aa,
    order.trans c b b' h.1 hb hb' (meet_bounds_d I order h).2 bb⟩

theorem Imp_d.adjoint_l {a b c d m : M.Domain} (order : Order_d I B R)
    (hd : M.mem d B) (h : Imp_d I B R a b c) (meet : Meet_d I B R d a m) :
    M.PairMember I d c R ↔ M.PairMember I m b R := by
  apply (h.2 d hd).trans
  exact ⟨fun all => all m meet,fun bound n hn => meet.unique_l I order hn ▸ bound⟩

theorem Boolean_d.neg_test_l (algebra : Boolean_d I B R z) {a b n m : M.Domain}
    (ha : M.mem a B) (hb : M.mem b B) (neg : Imp_d I B R b z n) (meet : Meet_d I B R a n m) :
    M.PairMember I a b R ↔ m = z := by
  obtain ⟨b',double⟩ := algebra.imp n z neg.1 algebra.bot_mem
  have double : Imp_d I B R n z b := algebra.double_neg b n b' hb neg double ▸ double
  exact (double.adjoint_l I algebra.order ha meet).trans
    ⟨fun bound => algebra.order.antisymm m z meet.1 algebra.bot_mem bound (algebra.bot_le m meet.1),
      fun eq => eq ▸ algebra.order.refl z algebra.bot_mem⟩

theorem Boolean_d.disjoint_l (algebra : Boolean_d I B R z) {a n d : M.Domain}
    (ha : M.mem a B) (hd : M.mem d B) (neg : Imp_d I B R a z n)
    (da : M.PairMember I d a R) (dn : M.PairMember I d n R) : d = z := by
  have dz := (neg.adjoint_l I algebra.order hd (meet_of_le_l I algebra.order hd ha da)).mp dn
  exact algebra.order.antisymm d z hd algebra.bot_mem dz (algebra.bot_le d hd)

end YesMetaZFC.SetTheory.BooleanZF
