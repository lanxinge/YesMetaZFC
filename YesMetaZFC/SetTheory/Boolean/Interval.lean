import YesMetaZFC.SetTheory.Boolean.CompleteHom

/-! # 内部布尔代数的主区间

区间载体由分离构造。交沿用原交，剩余为 u∧(a→b)；
区间内的任意集合族具有与原代数相同的上确界。
-/
namespace YesMetaZFC.SetTheory.BooleanZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

structure Bi_d (B R u A : M.Domain) : Prop where
  bound : M.mem u B
  carrier : ∀ a, M.mem a A ↔ M.mem a B ∧ M.PairMember I a u R

variable {B R z u A : M.Domain}

theorem Bi_d.meet_l (interval : Bi_d I B R u A) (source : Boolean_d I B R z)
    {a b c : M.Domain} (ha : M.mem a A) (hb : M.mem b A) :
    Meet_d I A R a b c ↔ Meet_d I B R a b c := by
  constructor
  · intro meet
    have hc := ((interval.carrier c).mp meet.1).1
    have bounds := (meet.2 c meet.1).mp (source.order.refl c hc)
    refine ⟨hc,fun d hd => ⟨fun dc => ⟨source.order.trans d c a hd hc ((interval.carrier a).mp ha).1 dc bounds.1,
      source.order.trans d c b hd hc ((interval.carrier b).mp hb).1 dc bounds.2⟩,?_⟩⟩
    intro h
    have du := source.order.trans d a u hd ((interval.carrier a).mp ha).1 interval.bound h.1 ((interval.carrier a).mp ha).2
    exact (meet.2 d ((interval.carrier d).mpr ⟨hd,du⟩)).mpr h
  · intro meet
    have cu := source.order.trans c a u meet.1 ((interval.carrier a).mp ha).1 interval.bound
      (meet_bounds_d I source.order meet).1 ((interval.carrier a).mp ha).2
    exact ⟨(interval.carrier c).mpr ⟨meet.1,cu⟩,fun d hd => meet.2 d ((interval.carrier d).mp hd).1⟩

theorem Bi_d.imp_l (interval : Bi_d I B R u A) (source : Boolean_d I B R z)
    {a b i c : M.Domain} (ha : M.mem a A)
    (imp : Imp_d I B R a b i) (meet : Meet_d I B R u i c) : Imp_d I A R a b c := by
  refine ⟨(interval.carrier c).mpr ⟨meet.1,(meet_bounds_d I source.order meet).1⟩,?_⟩
  intro d hd
  have bound := (interval.carrier d).mp hd
  apply (meet.2 d bound.1).trans
  apply (and_iff_right bound.2).trans
  apply (imp.2 d bound.1).trans
  exact ⟨fun all m hm => all m ((interval.meet_l I source hd ha).mp hm),
    fun all m hm => all m ((interval.meet_l I source hd ha).mpr hm)⟩

theorem Bi_d.boolean_l (interval : Bi_d I B R u A) (source : Boolean_d I B R z) : Boolean_d I A R z := by
  have sub a (ha : M.mem a A) := ((interval.carrier a).mp ha).1
  have hz := (interval.carrier z).mpr ⟨source.bot_mem,source.bot_le u interval.bound⟩
  have order : Order_d I A R := ⟨fun a ha => source.order.refl a (sub a ha),
    fun a b c ha hb hc => source.order.trans a b c (sub a ha) (sub b hb) (sub c hc),
    fun a b ha hb => source.order.antisymm a b (sub a ha) (sub b hb)⟩
  refine ⟨order,hz,(fun a ha => source.bot_le a (sub a ha)),?_,?_,?_⟩
  · intro a b ha hb
    obtain ⟨m,hm⟩ := source.meet a b (sub a ha) (sub b hb)
    exact ⟨m,(interval.meet_l I source ha hb).mpr hm⟩
  · intro a b ha hb
    obtain ⟨i,hi⟩ := source.imp a b (sub a ha) (sub b hb)
    obtain ⟨c,hc⟩ := source.meet u i interval.bound hi.1
    exact ⟨c,interval.imp_l I source ha hi hc⟩
  · intro a b c ha neg double
    have abot : M.PairMember I a c R := (double.2 a ha).mpr (fun m hm =>
      ((neg.2 b neg.1).mp (order.refl b neg.1)) m (meet_comm_d I hm))
    obtain ⟨n,hn⟩ := source.imp a z (sub a ha) source.bot_mem
    obtain ⟨m,hm⟩ := source.meet c n (sub c double.1) hn.1
    have bounds := meet_bounds_d I source.order hm
    have hmA := (interval.carrier m).mpr ⟨hm.1,source.order.trans m c u hm.1 (sub c double.1)
      interval.bound bounds.1 ((interval.carrier c).mp double.1).2⟩
    have mb : M.PairMember I m b R := (neg.2 m hmA).mpr (by
      intro l hl
      have lifted := (interval.meet_l I source hmA ha).mp hl
      have lb := meet_bounds_d I source.order lifted
      have ln := source.order.trans l m n lifted.1 hm.1 hn.1 lb.1 bounds.2
      exact (hn.adjoint_l I source.order lifted.1
        (meet_of_le_l I source.order lifted.1 (sub a ha) lb.2)).mp ln)
    obtain ⟨l,hl⟩ := source.meet c b (sub c double.1) (sub b neg.1)
    have lz := ((double.2 c double.1).mp (order.refl c double.1)) l
      ((interval.meet_l I source double.1 neg.1).mpr hl)
    have mz := source.order.trans m l z hm.1 hl.1 source.bot_mem ((hl.2 m hm.1).mpr ⟨bounds.1,mb⟩) lz
    have eq := source.order.antisymm m z hm.1 source.bot_mem mz (source.bot_le m hm.1)
    exact order.antisymm c a double.1 ha ((source.neg_test_l I (sub c double.1) (sub a ha) hn hm).mpr eq) abot

theorem Bi_d.sup_l (interval : Bi_d I B R u A) (source : Boolean_d I B R z)
    {D a : M.Domain} (sub : M.MemberSubset D A) : Bsup_d I A R D a ↔ Bsup_d I B R D a := by
  constructor
  · rintro ⟨ha,upper,least⟩
    refine ⟨((interval.carrier a).mp ha).1,upper,?_⟩
    intro b hb bound
    obtain ⟨c,meet⟩ := source.meet b u hb interval.bound
    have hc := (interval.carrier c).mpr ⟨meet.1,(meet_bounds_d I source.order meet).2⟩
    have ac := least c hc (fun x hx => (meet.2 x ((interval.carrier x).mp (sub x hx)).1).mpr
      ⟨bound x hx,((interval.carrier x).mp (sub x hx)).2⟩)
    exact source.order.trans a c b ((interval.carrier a).mp ha).1 meet.1 hb ac (meet_bounds_d I source.order meet).1
  · rintro ⟨ha,upper,least⟩
    exact ⟨(interval.carrier a).mpr ⟨ha,least u interval.bound (fun x hx => ((interval.carrier x).mp (sub x hx)).2)⟩,
      upper,fun b hb => least b ((interval.carrier b).mp hb).1⟩

theorem Bi_d.complete_l (interval : Bi_d I B R u A) (source : Cba_d I B R z) : Cba_d I A R z := by
  refine ⟨interval.boolean_l I source.toBoolean_d,?_⟩
  intro D sub
  have inside : M.MemberSubset D B := fun a ha => ((interval.carrier a).mp (sub a ha)).1
  obtain ⟨a,sup⟩ := source.sup D inside
  exact ⟨a,(interval.sup_l I source.toBoolean_d sub).mpr sup⟩

theorem bi_exists_l (hZF : M.Models ZF) (B R u : M.Domain) (hu : M.mem u B) : ∃ A, Bi_d I B R u A := by
  let ρ : Env M 2 := ⟨Fin.cases R (fun _ => u),fun _ => R⟩
  let φ : UnarySchema 2 := { body := Formula.orderedPairMem 𝒞 .newest (.bound 2) (.bound 1) }
  obtain ⟨A,values⟩ := ZF.separation_exists_d hZF φ ρ B
  exact ⟨A,hu,fun a => (values a).trans (and_congr_right fun _ => Formula.satisfies_orderedPairMem_iff I ..)⟩

end YesMetaZFC.SetTheory.BooleanZF
