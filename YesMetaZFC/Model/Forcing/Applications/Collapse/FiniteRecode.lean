import YesMetaZFC.SetTheory.Card.FiniteSequenceRecode
import YesMetaZFC.Model.Forcing.Stage.Transport
import YesMetaZFC.Model.Forcing.Stage.Generic
import YesMetaZFC.Model.Forcing.Internal.Forcing.OrderCongruence
import YesMetaZFC.Model.Forcing.Internal.Ground.Transfer

/-! # 有限坍缩的字母重编码

实际字母双射诱导完全序同构；目标泛型回拉后，其并图就是原泛型并图的逐项重编码。
因此对旧集合的稠密性调用可在原坍缩扩张内直接进行，不改变名称模型。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {M : SetTheory.Structure.{u}} {N : SetTheory.Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kpair_interpretation_l M (And.left hM) (KP.exists_pair (ZF.modelsKP hM))
local notation "J" => kpair_interpretation_l N (And.left hN) (KP.exists_pair (ZF.modelsKP hN))
include hi he

theorem fseq_recode_generic_l {ω X Y A B R S f : M.Domain} {U : M.Domain → Prop} {g : N.Domain}
    (hw : M.IsOmega ω) (sa : Fseq_space_d I ω X A) (sb : Fseq_space_d I ω Y B)
    (hf : M.IsSetBijectionFromTo I f X Y) (O : Cond_order_d M A R A)
    (ra : ∀ p q, Entry_d M p q R ↔ M.mem p A ∧ M.mem q A ∧ M.MemberSubset q p)
    (rb : ∀ p q, Entry_d M p q S ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p)
    (generic : Generic_d M B S B U) (fg : N.IsSetFunctionFromTo J g (e ω) (e Y))
    (onto : N.IsSetSurjectiveOnto J g (e ω) (e Y))
    (origin : ∀ p, U p → ∀ i y, Entry_d M i y p → Entry_d N (e i) (e y) g) :
    ∃ V : M.Domain → Prop, ∃ h, Generic_d M A R A V ∧ N.IsSetFunctionFromTo J h (e ω) (e X) ∧
      N.IsSetSurjectiveOnto J h (e ω) (e X) ∧
      ∀ p, V p → ∀ i x, Entry_d M i x p → Entry_d N (e i) (e x) h := by
  obtain ⟨F, bij, graph, sub⟩ := ZF.fseq_recode_l I hM hw sa sb hf
  obtain ⟨T, _, edges, L, embedding⟩ := order_transport_l hM O bij
  have orders x y (hx : M.mem x B) (hy : M.mem y B) : Entry_d M x y T ↔ Entry_d M x y S := by
    obtain ⟨p, hp, px⟩ := bij.2 x hx
    obtain ⟨q, hq, qy⟩ := bij.2 y hy
    refine (edges x y).trans ⟨?_, fun xy => ⟨p, q, px, qy, (ra p q).mpr ⟨hp, hq, ?_⟩⟩⟩
    · rintro ⟨p', q', px', qy', pq⟩
      exact (rb x y).mpr ⟨hx, hy, (sub q' p' y x qy' px').mp ((ra p' q').mp pq).2.2⟩
    · exact (sub q p y x qy px).mpr ((rb x y).mp xy).2.2
  have pulled := reg_generic_l O L hM embedding ((generic_order_l orders U).mpr generic)
  obtain ⟨j, inverse, back⟩ := ZF.exists_inverseBijectionWithPairs hM I hf
  have fj := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he inverse.1.1
  obtain ⟨h, fh, values⟩ := ZF.exists_compositionFunction hN J fg fj
  have edge {x y} (xy : Entry_d M x y j) : Entry_d N (e x) (e y) (e j) :=
    (image_entries_l e he inverse.1.1.1.1 (e x) (e y)).mpr ⟨x, y, xy, rfl, rfl⟩
  refine ⟨Pull_generic_d M F U, h, pulled, fh, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := (he X x).mp hx
    obtain ⟨b, hb, ba⟩ := inverse.2 a ha
    obtain ⟨i, hiω, ib⟩ := onto (e b) ((image_member_l e hi he).mpr hb)
    exact ⟨i, hiω, (values i (e a)).mpr ⟨hiω, e b, ib, edge ba⟩⟩
  · rintro p ⟨q, pq, hq⟩ i x ix
    obtain ⟨n, hn, fp⟩ := (sa p).mp ((graph p q).mp pq).1
    obtain ⟨y, _, xy⟩ := hf.1.1.2.2 x (fp.output_mem_of_pairMember ix)
    have iy := ((graph p q).mp pq).2.2 i y |>.mpr ⟨x, ix, xy⟩
    exact (values (e i) (e x)).mpr ⟨(image_member_l e hi he).mpr
      (hw.transitive hM n hn i (fp.input_mem_of_pairMember ix)), e y, origin q hq i y iy, edge ((back y x).mpr xy)⟩

end YesMetaZFC.Model.Forcing.Internal
