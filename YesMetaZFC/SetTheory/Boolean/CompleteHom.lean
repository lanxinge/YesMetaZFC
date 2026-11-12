import YesMetaZFC.SetTheory.Boolean.OrderLaws
import YesMetaZFC.SetTheory.FunctionConstruction

/-! # 模型内部的完全布尔同态

同态由实际集合函数图给出；完全性只量化原模型中的集合族。
像族的上确界直接由其全部图条目刻画，不要求调用者另交一张像集合。
-/
namespace YesMetaZFC.SetTheory.BooleanZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Bsup_d (B R A a : M.Domain) : Prop := M.mem a B ∧
  (∀ x, M.mem x A → M.PairMember I x a R) ∧
  ∀ b, M.mem b B → (∀ x, M.mem x A → M.PairMember I x b R) → M.PairMember I a b R

structure Cba_d (B R z : M.Domain) : Prop extends Boolean_d I B R z where
  sup : ∀ A, M.MemberSubset A B → ∃ a, Bsup_d I B R A a

structure Bh_d (B R z C S w F : M.Domain) : Prop where
  function : M.IsSetFunctionFromTo I F B C
  zero : M.PairMember I z w F
  meet : ∀ a b c a' b' c', M.PairMember I a a' F → M.PairMember I b b' F → M.PairMember I c c' F →
    Meet_d I B R a b c → Meet_d I C S a' b' c'
  neg : ∀ a n a' n', M.PairMember I a a' F → M.PairMember I n n' F →
    Imp_d I B R a z n → Imp_d I C S a' w n'

structure Cbh_d (B R z C S w F : M.Domain) : Prop extends Bh_d I B R z C S w F where
  sup : ∀ A a a', M.MemberSubset A B → Bsup_d I B R A a → M.PairMember I a a' F →
    (∀ x y, M.mem x A → M.PairMember I x y F → M.PairMember I y a' S) ∧
    ∀ d, M.mem d C → (∀ x y, M.mem x A → M.PairMember I x y F → M.PairMember I y d S) → M.PairMember I a' d S

theorem Bh_d.mono_l {B R z C S w F a b a' b' : M.Domain} (hom : Bh_d I B R z C S w F)
    (source : Boolean_d I B R z) (target : Boolean_d I C S w)
    (aa : M.PairMember I a a' F) (bb : M.PairMember I b b' F) (ab : M.PairMember I a b R) :
    M.PairMember I a' b' S := by
  have meet := hom.meet a b a a' b' a' aa bb aa (meet_of_le_l I source.order
    (hom.function.input_mem_of_pairMember aa) (hom.function.input_mem_of_pairMember bb) ab)
  exact (meet_bounds_d I target.order meet).2

end YesMetaZFC.SetTheory.BooleanZF
