import YesMetaZFC.Model.Forcing.Collapse.ProductCoordinates
import YesMetaZFC.Model.Forcing.Order.ProductRight
import YesMetaZFC.Model.Forcing.Boolean.DenseMap
import YesMetaZFC.Model.Forcing.TwoStep.ProductExtension
import YesMetaZFC.Model.Forcing.Ground.CheckPool
import YesMetaZFC.Model.Forcing.Collapse.ProductReflection
import YesMetaZFC.Model.Forcing.Ground.TreeShift
import YesMetaZFC.Model.Forcing.Embedding.Rank

/-! # 下一坐标块与旧前缀乘新坍缩的实际序同构

分解图将 t 送到〈t↾n,t(n)〉；满射由实际末项追加给出。
名字层随后消费这张同一图，无需另设乘积等价或泛型转移前提。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Fp_prefix_d.successor_map_l {ω A n m C S D V κ B U : M.Domain}
    (stage : Fp_prefix_d hZF ω A n C S) (next : Fp_prefix_d hZF ω A m D V)
    (hw : M.IsOmega ω) (hn : M.mem n ω) (hm : M.mem m ω) (succ : M.SuccessorOf m n)
    (fa : M.IsSetFunction I A) (alphabet : Entry_d M n κ A)
    (space : Fseq_space_d I ω κ B) (L : Cond_order_d M B U B)
    (order : ∀ s t, Entry_d M s t U ↔ M.mem s B ∧ M.mem t B ∧ M.MemberSubset t s) :
    ∃ J T F, Prod_d hZF C S B U J T ∧ Cond_order_d M J T J ∧
      M.IsSetBijectionFromTo I F D J ∧
      (∀ t v, Entry_d M t v F ↔ M.mem t D ∧ ∃ q s, KPair_d M v q s ∧ Fseq_end_d I ω t q s) ∧
      Dmap_d D V D J T J F := by
  obtain ⟨J,T,product,O⟩ := product_order_l hZF (stage.order_l hZF) L
  have split t (ht : M.mem t D) : ∃ q s, M.mem q C ∧ M.mem s B ∧ Fseq_end_d I ω t q s := by
    obtain ⟨q,s,fq,hs,ending⟩ := ((next.conditions t).mp ht).split_l hZF hw hn hm succ fa alphabet space
    exact ⟨q,s,(stage.conditions q).mpr fq,hs,ending⟩
  have typed {t q s} (ht : M.mem t D) (ending : Fseq_end_d I ω t q s) : M.mem q C ∧ M.mem s B := by
    obtain ⟨q',s',hq,hs,ending'⟩ := split t ht
    obtain ⟨eq,es⟩ := fseq_end_unique_l I hZF.1 ending' ending
    exact ⟨eq ▸ hq,es ▸ hs⟩
  let ρ : Env M 1 := ⟨fun _ => ω,fun _ => ω⟩
  let φ : BinarySchema 1 := { body := .existsE (.existsE (.conj
    (kpair_m (.bound 2) (.bound 1) .newest)
    (fseq_end_m (𝒞 := kpair_convention_l) (.bound 4) (.bound 3) (.bound 1) .newest))) }
  have sat t v : φ.denote ρ t v ↔ ∃ q s, KPair_d M v q s ∧ Fseq_end_d I ω t q s := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1,fseq_end_sat_l I hZF.1]
    rfl
  obtain ⟨F,fn,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := J)
    (fun t ht => by
      obtain ⟨q,s,_,_,ending⟩ := split t ht
      obtain ⟨v,pair⟩ := (I).total q s
      exact ⟨v,(sat t v).mpr ⟨q,s,pair,ending⟩⟩)
    (fun t _ v w hv hw => by
      obtain ⟨q,s,pair,ending⟩ := (sat t v).mp hv
      obtain ⟨q',s',pair',ending'⟩ := (sat t w).mp hw
      obtain ⟨eq,es⟩ := fseq_end_unique_l I hZF.1 ending ending'
      subst q' s'
      exact (I).unique pair pair')
    (fun t v ht tv => by
      obtain ⟨q,s,pair,ending⟩ := (sat t v).mp tv
      exact (product.pair v).mpr ⟨q,(typed ht ending).1,s,(typed ht ending).2,pair⟩)
  have edges t v : Entry_d M t v F ↔ M.mem t D ∧ ∃ q s, KPair_d M v q s ∧ Fseq_end_d I ω t q s :=
    (graph t v).trans (and_congr_right fun _ => sat t v)
  have bij : M.IsSetBijectionFromTo I F D J := by
    refine ⟨⟨fn,?_⟩,?_⟩
    · intro t u v tv uv
      obtain ⟨_,q,s,pair,ending⟩ := (edges t v).mp tv
      obtain ⟨_,q',s',pair',ending'⟩ := (edges u v).mp uv
      obtain ⟨eq,es⟩ := (I).injective pair pair'
      subst q' s'
      exact fseq_end_rebuild_l I hZF.1 ending ending'
    · intro v hv
      obtain ⟨q,hq,s,hs,pair⟩ := (product.pair v).mp hv
      obtain ⟨t,ft,ending⟩ := ((stage.conditions q).mp hq).snoc_l hZF hw hn succ alphabet ((space s).mp hs)
      have ht := (next.conditions t).mpr ft
      exact ⟨t,ht,(edges t v).mpr ⟨ht,q,s,pair,ending⟩⟩
  have mapped t u v w (tv : Entry_d M t v F) (uw : Entry_d M u w F) :
      Entry_d M v w T ↔ Entry_d M t u V := by
    obtain ⟨ht,q,s,pair,ending⟩ := (edges t v).mp tv
    obtain ⟨hu,q',s',pair',ending'⟩ := (edges u w).mp uw
    have tq := typed ht ending
    have uq := typed hu ending'
    have le := fp_snoc_order_l hZF ((stage.conditions q).mp tq.1).domain
      ((stage.conditions q').mp uq.1).domain ending ending'
    constructor
    · intro vw
      obtain ⟨_,_,a,b,c,d,pair₀,pair₁,ac,bd⟩ := (product.order v w).mp vw
      obtain ⟨eq,es⟩ := (I).injective pair₀ pair
      obtain ⟨eq',es'⟩ := (I).injective pair₁ pair'
      subst a b c d
      exact (next.order t u).mpr ⟨ht,hu,le.mpr ⟨((stage.order q q').mp ac).2.2,((order s s').mp bd).2.2⟩⟩
    · intro tu
      obtain ⟨old,last⟩ := le.mp ((next.order t u).mp tu).2.2
      exact (product.order v w).mpr ⟨fn.output_mem_of_pairMember tv,fn.output_mem_of_pairMember uw,
        q,s,q',s',pair,pair',(stage.order q q').mpr ⟨tq.1,uq.1,old⟩,(order s s').mpr ⟨tq.2,uq.2,last⟩⟩
  refine ⟨J,T,F,product,O,bij,edges,dmap_of_order_l O
    (fun t ht _ => (fn.2.2 t ht).imp fun _ hv => hv.2) ?_ fn.1.2 mapped ?_⟩
  · intro t v tv
    have ht := fn.input_mem_of_pairMember tv
    have hv := fn.output_mem_of_pairMember tv
    exact ⟨⟨ht,fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) D (eq ▸ ht)⟩,
      hv,fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) J (eq ▸ hv)⟩
  · intro v hv _
    obtain ⟨t,_,tv⟩ := bij.2 v hv
    exact ⟨t,v,tv,O.refl v hv⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 追加一个坍缩坐标保持整个有限前缀的泛型性

先使用真实二步扩张取得二元积泛型，再沿末项分解图回拉。
新前缀扩张与同一二步扩张保持地参数同构，供吸收的实数见证直接运输。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

def Fp_follow_d {C S b : M.Domain} {H : M.Domain → Prop} (ω D : M.Domain)
    (e : M.Domain → (extension_l M hZF C S b H).Domain)
    (K : (extension_l M hZF C S b H).Domain → Prop) (t : M.Domain) : Prop :=
  M.mem t D ∧ ∃ q s, Fseq_end_d I ω t q s ∧ H q ∧ K (e s)

theorem Fp_prefix_d.successor_generic_l {ω A n m C S D V κ B U W a : M.Domain}
    (stage : Fp_prefix_d hZF ω A n C S) (next : Fp_prefix_d hZF ω A m D V)
    (hw : M.IsOmega ω) (hn : M.mem n ω) (hm : M.mem m ω) (succ : M.SuccessorOf m n)
    (fa : M.IsSetFunctionFromTo I A ω W) (alphabet : Entry_d M n κ A)
    (space : Fseq_space_d I ω κ B) (L : Cond_order_d M B U B)
    (order : ∀ s t, Entry_d M s t U ↔ M.mem s B ∧ M.mem t B ∧ M.MemberSubset t s)
    {H : M.Domain → Prop} (small : Generic_d M C S C H) (ha : H a)
    (e : M.Domain → (extension_l M hZF C S C H).Domain)
    (ei : Function.Injective e)
    (ef : ∀ x y, (extension_l M hZF C S C H).mem y (e x) ↔ ∃ z, M.mem z x ∧ e z = y)
    (checks : ∀ x t, Check_d M a x t → Qval_d M C S C H t (e x))
    {K : (extension_l M hZF C S C H).Domain → Prop}
    (big : Generic_d (extension_l M hZF C S C H) (e B) (e U) (e B) K) :
    Generic_d M D V D (Fp_follow_d hZF ω D e K) ∧
      Miso_over_d (extension_l M hZF D V D (Fp_follow_d hZF ω D e K))
        (extension_l (extension_l M hZF C S C H) (preserves_zf_l (stage.order_l hZF) hZF small)
          (e B) (e U) (e B) K)
        (Gval_d M D V D (Fp_follow_d hZF ω D e K))
        (fun x => Gval_d (extension_l M hZF C S C H) (e B) (e U) (e B) K (e x)) := by
  have O := stage.order_l hZF
  have O' := next.order_l hZF
  have hE := preserves_zf_l O hZF small
  obtain ⟨J,T,F,product,OP,bij,edges,map⟩ :=
    stage.successor_map_l hZF next hw hn hm succ fa.1 alphabet space L order
  obtain ⟨b,hb,top⟩ := stage.top_l hZF hw hn fa
  have accepted := small.upward a b ha hb (top a (small.proper a ha).1)
  have canonical := check_map_change_l O hZF small ha accepted e checks
  have bigOrder := image_cond_order_l (ZF.modelsKP hZF) hE.1 e ei ef L
  obtain ⟨generic,iso⟩ := product.extension_l hZF O L OP top small accepted e canonical
    (fun _ _ _ _ => Iff.rfl) bigOrder big
  have reg := map.regular_l OP
  obtain ⟨p,hp⟩ := generic.inhabited
  have hit := reg.dense_hit_l hZF OP generic hp (fun q hq => map.dense q hq.1 hq.2.1)
  have newGeneric := reg_generic_l O' OP hZF reg generic hit
  have newIso := (map.ground_l hZF O' OP generic).trans_l iso
  have same : Pull_generic_d M F (Prod_generic_d hZF J e K) = Fp_follow_d hZF ω D e K := by
    funext t
    apply propext
    constructor
    · rintro ⟨v,tv,_,q,s,pair,hq,hs⟩
      obtain ⟨ht,q',s',pair',ending⟩ := (edges t v).mp tv
      obtain ⟨eq,es⟩ := (I).injective pair' pair
      subst q' s'
      exact ⟨ht,q,s,ending,hq,hs⟩
    · rintro ⟨ht,q,s,ending,hq,hs⟩
      obtain ⟨v,pair⟩ := (I).total q s
      have tv := (edges t v).mpr ⟨ht,q,s,pair,ending⟩
      exact ⟨v,tv,bij.1.1.output_mem_of_pairMember tv,q,s,pair,hq,hs⟩
  exact ⟨same ▸ newGeneric,same ▸ newIso⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 实际背景滤子列的前缀泛型保持

把末项分解的泛型精确识别为旧滤子列追加 K 后的逐坐标接受谓词，
再由背景分离得到同一个新前缀滤子集合；它的扩张与原二步扩张保持地参数同构。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {N : Structure.{u}} {M : Structure.{v}} (hN : N.Models ZF) (hM : M.Models ZF)
local notation "I" => kpair_interpretation_l N (And.left hN) (KP.exists_pair (ZF.modelsKP hN))
local notation "J" => kpair_interpretation_l M (And.left hM) (KP.exists_pair (ZF.modelsKP hM))
variable (k : N.Domain → M.Domain) (ki : Function.Injective k)
  (kf : ∀ a y, M.mem y (k a) ↔ ∃ x, N.mem x a ∧ k x = y)
variable {ω A n m C S D V κ B U W a : N.Domain} {F F' K : M.Domain}
local notation "H" => (fun q : N.Domain => N.mem q C ∧ Fp_ready_d J (k n) F (k q))
local notation "E" => extension_l N hN C S C H
include ki kf

theorem fp_ground_successor_l (stage : Fp_prefix_d hN ω A n C S) (next : Fp_prefix_d hN ω A m D V)
    (hw : N.IsOmega ω) (hn : N.mem n ω) (hm : N.mem m ω) (succ : N.SuccessorOf m n)
    (fa : N.IsSetFunctionFromTo I A ω W) (alphabet : Entry_d N n κ A)
    (space : Fseq_space_d I ω κ B) (L : Cond_order_d N B U B)
    (order : ∀ s t, Entry_d N s t U ↔ N.mem s B ∧ N.mem t B ∧ N.MemberSubset t s)
    (small : Generic_d N C S C H) (ha : H a)
    (e : N.Domain → (E).Domain) (ei : Function.Injective e)
    (ef : ∀ x y, (E).mem y (e x) ↔ ∃ z, N.mem z x ∧ e z = y)
    (checks : ∀ x t, Check_d N a x t → Qval_d N C S C H t (e x))
    (big : Generic_d E (e B) (e U) (e B) (Em_generic_d e (fun s => M.mem (k s) K)))
    (ff : M.IsSetFunction J F') (keep : M.IsRestrictionOf J F F' (k n)) (last : M.PairMember J (k n) K F') :
    ∃ Z, M.MemberSubset Z (k D) ∧
      (∀ t, M.mem t Z ↔ M.mem t (k D) ∧ Fp_ready_d J (k m) F' t) ∧
      Generic_d N D V D (fun q => M.mem (k q) Z) ∧
      Miso_over_d (extension_l N hN D V D (fun q => M.mem (k q) Z))
        (extension_l E (preserves_zf_l (stage.order_l hN) hN small)
          (e B) (e U) (e B) (Em_generic_d e (fun s => M.mem (k s) K)))
        (Gval_d N D V D (fun q => M.mem (k q) Z))
        (fun x => Gval_d E (e B) (e U) (e B) (Em_generic_d e (fun s => M.mem (k s) K)) (e x)) := by
  have nextGeneric := stage.successor_generic_l hN next hw hn hm succ fa alphabet space L order small ha e ei ef checks big
  have read {t q s} (ht : N.mem t D) (hq : N.mem q C) (ending : Fseq_end_d I ω t q s) :
      Fp_ready_d J (k m) F' (k t) ↔ Fp_ready_d J (k n) F (k q) ∧ M.mem (k s) K := by
    have ft := (next.conditions t).mp ht
    obtain ⟨m₀,n₀,data⟩ := ending
    have en := data.prefix_sequence.2.2.2.eq hN.1 ((stage.conditions q).mp hq).domain
    subst n₀
    have seq : N.IsSequenceOfLength I t m :=
      ⟨hw.members_areOrdinals (ZF.modelsKP hN) m hm,ft.function,ft.domain⟩
    have ft' := image_sequence_l hN hM k ki kf seq
    have cut' := image_restriction_l hN hM k ki kf ft.function.1 data.prefix_restriction
    have point := (image_entry_iff_l k ki kf (KP.exists_pair (ZF.modelsKP hN)) hM.1 n s t).mp data.last_value
    exact fp_ready_snoc_l J hM.1 (image_successor_l (hEN := hM.1) k ki kf hN.1 succ)
      ft'.2.1 cut' point ff keep last
  have accepted s : Em_generic_d e (fun s => M.mem (k s) K) (e s) ↔ M.mem (k s) K :=
    ⟨fun ⟨t,ht,eq⟩ => congrArg k (ei eq) ▸ ht,fun hs => ⟨s,hs,rfl⟩⟩
  have follows t : Fp_follow_d hN ω D e (Em_generic_d e (fun s => M.mem (k s) K)) t ↔
      N.mem t D ∧ Fp_ready_d J (k m) F' (k t) := by
    constructor
    · rintro ⟨ht,q,s,ending,⟨hq,ready⟩,hs⟩
      exact ⟨ht,(read ht hq ending).mpr ⟨ready,(accepted s).mp hs⟩⟩
    · rintro ⟨ht,ready⟩
      obtain ⟨q,s,fq,_,ending⟩ := ((next.conditions t).mp ht).split_l hN hw hn hm succ fa.1 alphabet space
      have hq := (stage.conditions q).mpr fq
      obtain ⟨old,new⟩ := (read ht hq ending).mp ready
      exact ⟨ht,q,s,ending,⟨hq,old⟩,(accepted s).mpr new⟩
  obtain ⟨Z,members⟩ := fp_ready_filter_l J hM (k m) F' (k D)
  have same : Fp_follow_d hN ω D e (Em_generic_d e (fun s => M.mem (k s) K)) = (fun q => M.mem (k q) Z) := by
    funext q
    apply propext
    exact (follows q).trans ((members (k q)).trans
      (and_congr (image_member_l k ki kf) Iff.rfl)).symm
  rw [same] at nextGeneric
  exact ⟨Z,fun t ht => ((members t).mp ht).1,members,nextGeneric⟩

end YesMetaZFC.Model.Forcing.Internal
