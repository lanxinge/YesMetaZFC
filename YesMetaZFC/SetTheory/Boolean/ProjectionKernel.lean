import YesMetaZFC.SetTheory.Boolean.Kernel
import YesMetaZFC.SetTheory.Boolean.Projection

/-! # 主区间投影的核约化实例

实际构造相交投影并调用通用核定理。其核上确界恰为 ¬u，忠实限制的
载体恰为原主区间；所得限制为该区间上的实际双射完全同态。
-/
namespace YesMetaZFC.SetTheory.BooleanZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
include hZF

theorem Cba_d.project_kernel_l {B R z u : M.Domain} (source : Cba_d I B R z) (hu : M.mem u B) :
    ∃ A F N k G, Bi_d I B R u A ∧ Cba_d I A R z ∧ Cbh_d I B R z A R z F ∧
      (∀ a b, M.PairMember I a b F ↔ M.mem a B ∧ Meet_d I B R a u b) ∧
      (∀ a, M.mem a N ↔ M.mem a B ∧ M.PairMember I a z F) ∧ Bsup_d I B R N k ∧
      Imp_d I B R u z k ∧ (∀ a, M.mem a B → (M.PairMember I a z F ↔ M.PairMember I a k R)) ∧
      M.IsRestrictionOf I G F A ∧ Cbh_d I A R z A R z G ∧ M.IsSetBijectionFromTo I G A A := by
  obtain ⟨A,interval⟩ := bi_exists_l I hZF B R u hu
  have algebra := interval.complete_l I source
  obtain ⟨F,hom,graph⟩ := interval.project_l I hZF source.toBoolean_d
  obtain ⟨N,k,v,D,G,kernel,sup,kz,neg,domain,cut,_,reduced,injective,principal,_,range⟩ :=
    hom.kernel_l I hZF source algebra.toBoolean_d
  obtain ⟨n,complement⟩ := source.imp u z hu source.bot_mem
  have kn : M.PairMember I k n R := (complement.adjoint_l I source.order sup.1 ((graph k z).mp kz).2).mpr
    (source.order.refl z source.bot_mem)
  obtain ⟨t,ht,nt⟩ := hom.function.2.2 n complement.1
  have tz := (complement.adjoint_l I source.order complement.1 ((graph n t).mp nt).2).mp
    (source.order.refl n complement.1)
  have teq := source.order.antisymm t z ((interval.carrier t).mp ht).1 source.bot_mem tz
    (source.bot_le t ((interval.carrier t).mp ht).1)
  have nk := (principal n complement.1).mp (teq ▸ nt)
  have eq := source.order.antisymm k n sup.1 complement.1 kn nk
  have complement : Imp_d I B R u z k := eq.symm ▸ complement
  have vu := source.double_neg u k v hu complement neg
  subst v
  have eq : D = A := hZF.1.eq_of_same_members D A (fun a => (domain a).trans (interval.carrier a).symm)
  subst D
  have onto : M.IsSetSurjectiveOnto I G A A := by
    intro y hy
    have yy : M.PairMember I y y F := (graph y y).mpr ⟨((interval.carrier y).mp hy).1,
      meet_of_le_l I source.order ((interval.carrier y).mp hy).1 hu ((interval.carrier y).mp hy).2⟩
    obtain ⟨a,ay⟩ := range y y yy
    exact ⟨a,injective.1.input_mem_of_pairMember ay,ay⟩
  exact ⟨A,F,N,k,G,interval,algebra,hom,graph,kernel,sup,complement,principal,cut,reduced,injective,onto⟩

end YesMetaZFC.SetTheory.BooleanZF
