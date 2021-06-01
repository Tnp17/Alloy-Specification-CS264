sig Name, Faculty, Bill {}
sig Info
{	 info : Name -> lone Faculty    }
sig Student{}
sig Subject
{	subject : Student -> lone Form	}
sig Form
{      write_form : Student -> some Form,
       oldInfo : Student -> lone Info,
       avsApprove : Student -> lone Advisor,
       lecApprove : Student -> some Lecturer,
   	 staffApprove : Student -> lone StaffMajor,
       deanApprove : StaffMajor -> lone Dean,
       sentBack : Dean -> lone StaffMajor,
       regApprove : StaffMajor -> lone Registrar
}
sig Advisor
{	AvsApprove : Form	}
sig Lecturer
{   	LecApprove : Form	}
sig StaffMajor
{	StaffApprove : Form   }
sig Dean
{	DeanApprove : Form    }
sig Registrar
{	 RegApprove : Form,
   	 sentBill : Bill -> lone Student
}
pred studentWrite (f,f': Form, s: Student, i: Info)
{	#f.write_form = 0
    	f'.write_form = f.write_form + s->f
}
pred advisorWrite (f,f': Form, a: Advisor, s: Student)
{	#f'.write_form = 1
	#f.avsApprove = 0
	f'.avsApprove = f.avsApprove + s->a
}
pred lecturerWrite (f,f': Form, lec: Lecturer, s: Student)
{	#f'.write_form = 1
	#f'.avsApprove = 1
	#f.lecApprove = 0
	f'.lecApprove = f.lecApprove + s->lec
}
pred staffWriteandCheck (f,f': Form, stf: StaffMajor, s: Student)
{	#f'.write_form = 1
	#f'.avsApprove = 1
	#f'.lecApprove = 1
	#f.staffApprove = 0
	f'.staffApprove = f.staffApprove + s->stf
}
pred deanWrite (f,f': Form, d: Dean, stf: StaffMajor)
{	#f'.write_form = 1
	#f'.avsApprove = 1
	#f'.lecApprove = 1
	#f'.staffApprove = 1
	f'.deanApprove = f.deanApprove + stf->d
}
pred regWriteandCheck (f,f': Form, stf: StaffMajor, r: Registrar)
{	#f'.write_form = 1
	#f'.avsApprove = 1
	#f'.lecApprove = 1
	#f'.staffApprove = 1
	#f'.deanApprove = 1
	#f.regApprove = 0
	f'.regApprove = f.regApprove + stf->r
}
pred sent (f,f': Form, r,r': Registrar, d: Dean, stf: StaffMajor, s: Student, b: Bill)
{	#f.sentBack = 0
	#r.sentBill = 0
	f'.sentBack = f.sentBack + d->stf
	r'.sentBill = r.sentBill + b->s
}
fun lookup_info (i: Info, n: Name) : set Faculty {n.(i.info)}
fun lookup_studentWrite (f: Form, s: Student) : set Form {s.(f.write_form)}
fun lookup_advisorWrite (f: Form, s: Student) : set Advisor {s.(f.avsApprove)}
fun lookup_lecturerWrite (f: Form, s: Student) : set Lecturer {s.(f.lecApprove)}
fun lookup_staffWriteandCheck (f: Form, s: Student) : set StaffMajor {s.(f.staffApprove)}
fun lookup_deanWrite (f: Form, stf: StaffMajor) : set Dean {stf.(f.deanApprove)}
fun lookup_regWriteandCheck (f: Form, stf : StaffMajor) : set Registrar {stf.(f.regApprove)}
pred showWrite (f,f' : Form)
{	#f'.write_form = 1	
	#f'.avsApprove = 1
	#f'.lecApprove = 1
	#f'.staffApprove = 1
	#f'.deanApprove = 1
	#f'.regApprove = 1    
}
run showWrite {} for 1

