import YesMetaZFC.SetTheory.Ord.Code.BoundedOrder
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph
import YesMetaZFC.SetTheory.KP.OrdinalCore

/-! # 规范代码方块的实际 Δ₀ 坍塌证书

有界矩阵检查完整方块、满射函数和次序保持。向背景读回后，原典范
良序及坍塌方程由这些检查恢复，因此每个图值都是原 Oc_pair_d 代码。
值域为一个序数，故同一张图完整覆盖任何已登记代码的全部前驱。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Oc_square_d (t X η F : M.Domain) : Prop := M.IsOrdinal t ∧ Oc_grid_d t X ∧
  M.IsOrdinal η ∧ Fn0_d X η F ∧
  (∀ d, M.mem d η → ∃ p, M.mem p X ∧ Rd_entry_d p d F) ∧
  ∀ p, M.mem p X → ∀ q, M.mem q X → ∀ d, M.mem d η → ∀ e, M.mem e η →
    Rd_entry_d p d F → Rd_entry_d q e F → (Oc_less_d t p q ↔ M.mem d e)

def oc_square_m {d} (t X η F : Term d) : Formula 1 d := set[d] ⟪
  ⌜KP.ord0_m⌝ₚ(⌜t⌝ₛ) ∧ ⌜oc_grid_m⌝ₚ(⌜t⌝ₛ,⌜X⌝ₛ) ∧ ⌜KP.ord0_m⌝ₚ(⌜η⌝ₛ) ∧
  ⌜fn0_m⌝ₚ(⌜X⌝ₛ,⌜η⌝ₛ,⌜F⌝ₛ) ∧
  (∀ d ∈ ⌜η⌝ₛ, ∃ p ∈ ⌜X⌝ₛ, ⌜rd_entry0_m⌝ₚ(p,d,⌜F⌝ₛ)) ∧
  (∀ p ∈ ⌜X⌝ₛ, ∀ q ∈ ⌜X⌝ₛ, ∀ d ∈ ⌜η⌝ₛ, ∀ e ∈ ⌜η⌝ₛ,
    ⌜rd_entry0_m⌝ₚ(p,d,⌜F⌝ₛ) → ⌜rd_entry0_m⌝ₚ(q,e,⌜F⌝ₛ) →
      (⌜oc_less_m⌝ₚ(⌜t⌝ₛ,p,q) ↔ d ∈ e))⟫
derive_free_closed oc_square_m

theorem oc_square_delta_l {d} (t X η F : Term d) : (oc_square_m t X η F).IsDelta0 :=
  .conj (KP.ord0_delta_l _) (.conj (oc_grid_delta_l ..) (.conj (KP.ord0_delta_l _) (.conj (fn0_delta_l ..)
    (.conj (.forallMem _ (.existsMem _ (rd_entry0_delta_l ..)))
      (.forallMem _ (.forallMem _ (.forallMem _ (.forallMem _
        (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.iff (oc_less_delta_l ..) (.mem _ _))))))))))))

theorem oc_square_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (t X η F : Term d) :
    Formula.satisfies ρ (oc_square_m t X η F) ↔ Oc_square_d (t.eval ρ) (X.eval ρ) (η.eval ρ) (F.eval ρ) := by
  simp only [oc_square_m,Oc_square_d,Formula.satisfies_conj_iff,KP.ord0_sat_l hKP,oc_grid_sat_l hKP.1,
    fn0_sat_l hKP.1,Formula.satisfies_forallMem_iff,Formula.satisfies_existsMem_iff,rd_entry0_sat_l hKP.1,
    Formula.satisfies_imp_iff,Formula.satisfies_iff_iff,oc_less_sat_l hKP.1,Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

include hZF

/-- 有界次序同构恢复原良序坍塌的每个成员方程。 -/
theorem Oc_square_d.collapse_l {t X η F : M.Domain} (cert : Oc_square_d t X η F) :
    ∃ R, M.IsCanonicalOrdinalPairOrder I R X t ∧ M.IsWellOrderCollapseFunction I F R X X ∧ M.IsRangeOf I η F := by
  obtain ⟨ordinal,grid,rangeOrdinal,fn,onto,compare⟩ := cert
  have product := (oc_grid_read_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF))).mp grid
  obtain ⟨R,order,_⟩ := ZF.exists_canonicalOrdinalPairWellOrder hZF I ordinal product
  have ff := fn0_function_l (ZF.modelsKP hZF) fn
  refine ⟨R,order,⟨ff.1,ff.2.1,⟨fun _ h => h,fun _ _ _ h _ => h⟩,?_⟩,?_⟩
  · intro p hp d pd e
    have hd := (fn.bound_l pd).2
    constructor
    · intro ed
      have he := rangeOrdinal.transitive d hd e ed
      obtain ⟨q,hq,qe⟩ := onto e he
      exact ⟨q,hq,(order.2.2 q p).mpr ⟨hq,hp,
        (oc_less_read_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) grid hq hp).mp
          ((compare q hq p hp e he d hd qe pd).mpr ed)⟩,qe⟩
    · rintro ⟨q,hq,qp,qe⟩
      exact (compare q hq p hp e (fn.bound_l qe).2 d hd qe pd).mp
        ((oc_less_read_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) grid hq hp).mpr ((order.2.2 q p).mp qp).2.2)
  · intro d
    exact ⟨fun hd => (onto d hd).elim fun p h => ⟨p,h.2⟩,fun ⟨p,pd⟩ => (fn.bound_l pd).2⟩

theorem oc_square_exists_l {t X : M.Domain} (ordinal : M.IsOrdinal t) (product : M.IsCartesianProduct I X t t) :
    ∃ η F, Oc_square_d t X η F := by
  obtain ⟨R,order,well⟩ := ZF.exists_canonicalOrdinalPairWellOrder hZF I ordinal product
  obtain ⟨η,⟨F,collapse,range⟩,_⟩ := ZF.wellOrderType_existsUnique hZF I well
  have grid := (oc_grid_read_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF))).mpr product
  have target : M.IsOrdinal η := Structure.IsWellOrderType.isOrdinal hZF I well ⟨F,collapse,range⟩
  have fn : M.IsSetFunctionFromTo I F X η := ⟨collapse.1,collapse.2.1,fun p hp => by
    obtain ⟨d,pd⟩ := (collapse.2.1 p).mp hp
    exact ⟨d,(range d).mpr ⟨p,pd⟩,pd⟩⟩
  refine ⟨η,F,ordinal,grid,target,fn0_of_function_l (ZF.modelsKP hZF) fn,?_,?_⟩
  · intro d hd
    obtain ⟨p,pd⟩ := (range d).mp hd
    exact ⟨p,fn.input_mem_of_pairMember pd,pd⟩
  · intro p hp q hq d _ e _ pd qe
    have edges : M.PairMember I p q R ↔ M.CanonicalOrdinalPairLess I p q :=
      (order.2.2 p q).trans ⟨fun h => h.2.2,fun h => ⟨hp,hq,h⟩⟩
    exact (oc_less_read_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) grid hp hq).trans
      (edges.symm.trans (collapse.relation_iff_mem hZF I well pd qe))

/-- 原代码选择一个实际完整方块图，原配对对象和代码值均保持。 -/
theorem oc_pair_square_l {a b c : M.Domain} (code : Oc_pair_d I a b c) :
    ∃ t X η F p, Oc_square_d t X η F ∧ KPair_d M p a b ∧ M.mem p X ∧ Rd_entry_d p c F := by
  obtain ⟨t,p,pair,ordinal,X,R,order,hp,value⟩ := code
  obtain ⟨η,F,cert⟩ := oc_square_exists_l hZF ordinal order.1
  obtain ⟨R',order',collapse,_⟩ := cert.collapse_l hZF
  exact ⟨t,X,η,F,p,cert,pair,hp,oc_at_function_l I hZF ordinal order' collapse hp ⟨ordinal,X,R,order,hp,value⟩⟩

/-- 图覆盖值域内每个全局规范代码；因值域传递，特别覆盖当前代码的全部前驱。 -/
theorem Oc_square_d.codes_l {t X η F : M.Domain} (cert : Oc_square_d t X η F) (a b c : M.Domain) :
    Oc_pair_d I a b c ∧ M.mem c η ↔ ∃ p, M.mem p X ∧ KPair_d M p a b ∧ Rd_entry_d p c F := by
  obtain ⟨R,order,collapse,_⟩ := cert.collapse_l hZF
  have well := order.isSetCodedWellOrder hZF cert.1
  have value p (hp : M.mem p X) d (pd : Rd_entry_d p d F) :
      ∃ x y, KPair_d M p x y ∧ Oc_pair_d I x y d := by
    obtain ⟨x,_,y,_,pair⟩ := cert.2.1.1 p hp
    exact ⟨x,y,pair,t,p,pair,cert.1,X,R,order,hp,collapse.collapseValue_of_pairMember hZF I well hp pd⟩
  constructor
  · rintro ⟨code,hc⟩
    obtain ⟨p,hp,pc⟩ := cert.2.2.2.2.1 c hc
    obtain ⟨x,y,pair,code'⟩ := value p hp c pc
    obtain ⟨ex,ey⟩ := oc_pair_injective_l I hZF code' code
    subst x y
    exact ⟨p,hp,pair,pc⟩
  · rintro ⟨p,hp,pair,pc⟩
    obtain ⟨x,y,pair',code⟩ := value p hp c pc
    obtain ⟨ex,ey⟩ := kpair_injective_l M pair' pair
    subst x y
    exact ⟨code,(cert.2.2.2.1.bound_l pc).2⟩

end YesMetaZFC.SetTheory
