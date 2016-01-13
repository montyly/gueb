from javax.swing import *
from java.awt import *
from export_protobuf import *
from time import sleep

class ExportBin6ToGUEB:

  def listSelect(self,event) :
    selected = self.list.getSelectedValues()
    if(self.alloc == []) :
        self.alloc=selected
        self.list.clearSelection()
        self.label_2.setText(' Select Free functions')

        free = [ x for x in self.data if "free" in x.lower() or "realloc" in x.lower()]
        other = [ x for x in self.data if x not in free]
        
        self.list.setListData(free+other)
        self.list.getSelectionModel().setSelectionInterval(0, len(free)-1)

    else:
        self.free=selected
        self.frame.setVisible(False)
        print('Start exporting')
        export_mod(self.module,self.alloc,self.free) 
        print('######################\nEnd exporting\n')
        print('Protobuf file : %s'%self.name)
        print('Entry point file : %s\n'%(self.name+'-entry-points'))
        exit(0) 


  def cbSelectMod(self,event):
    selected = self.cb_module.selectedIndex
    if selected >= 0:
        self.name = self.data[selected]
        print("Module selected %s"%self.name)
        self.frame.setVisible(False)
        frame = self.frame
      
        self.module = find_mod(self.db,self.name)
        self.data = list_func(self.module)

        self.data.sort()

        
        frame.remove(self.panel_1)
        frame.remove(self.label_1)
        frame.remove(self.btn_1)

        alloc = [ x for x in self.data if  "alloc" in x.lower()]
        other = [ x for x in self.data if x not in alloc]
        
        self.list = JList(alloc+other)
        self.list.getSelectionModel().setSelectionInterval(0, len(alloc)-1)

        spane = JScrollPane()
        spane.setPreferredSize(Dimension(400,450))
        spane.getViewport().setView((self.list))

        panel_2 = JPanel()
        self.panel_2 = panel_2
        panel_2.add(spane)
        frame.add(panel_2,BorderLayout.CENTER)

        btn_2 = JButton('Ok',actionPerformed=self.listSelect)
        self.btn_2=btn_2
        frame.add(btn_2,BorderLayout.SOUTH)
        self.label_2 = JLabel(' Select Alloc functions')
        frame.add(self.label_2,BorderLayout.NORTH)
        frame.pack()
        frame.setLocationRelativeTo(None);
        frame.setVisible(True)

  def __init__(self):
    self.alloc = []
    self.free = []
    frame = JFrame("Gueb Export")
    frame.setLocationRelativeTo(None)

    self.frame = frame
    frame.setSize(250, 100)
    frame.setLayout(BorderLayout())

    self.db = connect(binnavi_host,binnavi_db_name,binnavi_db_username,binnavi_db_password,binnavi_collab_name)
    data = list_modules(self.db)    
    self.data = (data)

    self.panel_1 = JPanel()
    self.label_1 = JLabel('Select the module', SwingConstants.CENTER)
    self.cb_module = JComboBox(self.data)
    self.btn_1 = JButton('Load',actionPerformed=self.cbSelectMod)
    
    self.panel_1.add(self.label_1)
    self.panel_1.add(self.cb_module)
    self.panel_1.add(self.btn_1)

    frame.add(self.panel_1,BorderLayout.CENTER)
    frame.setDefaultCloseOperation(WindowConstants.EXIT_ON_CLOSE)
    frame.setVisible(True)

if __name__ == '__main__':
        ExportBin6ToGUEB()
