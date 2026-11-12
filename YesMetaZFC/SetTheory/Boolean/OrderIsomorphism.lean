import YesMetaZFC.SetTheory.Boolean.CompleteHom

/-! # 完备布尔代数的实际序同构自动保持全部运算 -/
namespace YesMetaZFC.SetTheory.BooleanZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Cba_d.order_iso_l {B R z C S w F : M.Domain} (source : Cba_d I B R z)
    (target : Boolean_d I C S w) (bij : M.IsSetBijectionFromTo I F B C)
    (order : ∀ a b x y, M.PairMember I a x F → M.PairMember I b y F →
      (M.PairMember I x y S ↔ M.PairMember I a b R)) : Cbh_d I B R z C S w F := by
  have fn := bij.1.1
  have zero : M.PairMember I z w F := by
    obtain ⟨x,hx,zx⟩ := fn.2.2 z source.bot_mem
    obtain ⟨a,ha,aw⟩ := bij.2 w target.bot_mem
    have eq := target.order.antisymm x w hx target.bot_mem
      ((order z a x w zx aw).mpr (source.bot_le a ha)) (target.bot_le x hx)
    exact eq ▸ zx
  have meet a b c x y v (ax : M.PairMember I a x F) (by' : M.PairMember I b y F)
      (cv : M.PairMember I c v F) (h : Meet_d I B R a b c) : Meet_d I C S x y v := by
    refine ⟨fn.output_mem_of_pairMember cv,fun d hd => ?_⟩
    obtain ⟨e,he,ed⟩ := bij.2 d hd
    exact (order e c d v ed cv).trans ((h.2 e he).trans
      (and_congr (order e a d x ed ax).symm (order e b d y ed by').symm))
  refine ⟨⟨fn,zero,meet,?_⟩,?_⟩
  · intro a n x y ax ny neg
    refine ⟨fn.output_mem_of_pairMember ny,fun d hd => ?_⟩
    obtain ⟨e,he,ed⟩ := bij.2 d hd
    apply (order e n d y ed ny).trans ((neg.2 e he).trans ?_)
    constructor
    · intro all m hm
      obtain ⟨c,hc⟩ := source.meet e a he (fn.input_mem_of_pairMember ax)
      obtain ⟨v,_,cv⟩ := fn.2.2 c hc.1
      have eq := (meet e a c d x v ed ax cv hc).unique_l I target.order hm
      exact eq ▸ (order c z v w cv zero).mpr (all c hc)
    · intro all c hc
      obtain ⟨v,_,cv⟩ := fn.2.2 c hc.1
      exact (order c z v w cv zero).mp (all v (meet e a c d x v ed ax cv hc))
  · intro A a x sub sup ax
    refine ⟨fun b y hb by' => (order b a y x by' ax).mpr (sup.2.1 b hb),fun d hd upper => ?_⟩
    obtain ⟨e,he,ed⟩ := bij.2 d hd
    apply (order a e x d ax ed).mpr
    apply sup.2.2 e he
    intro b hb
    obtain ⟨y,_,by'⟩ := fn.2.2 b (sub b hb)
    exact (order b e y d by' ed).mp (upper b y hb by')

end YesMetaZFC.SetTheory.BooleanZF
